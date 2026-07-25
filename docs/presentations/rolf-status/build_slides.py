#!/usr/bin/env python3
"""Build slides.html from slides.md. See the comment atop slides.md for the
conventions. Images are inlined as data URIs so slides.html stays
self-contained."""

import base64
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
MD = os.path.join(HERE, 'slides.md')
OUT = os.path.join(HERE, 'slides.html')


def esc(s):
    return s.replace('&', '&amp;').replace('<', '&lt;').replace('>', '&gt;')


def inline(s):
    """Backticks to <code>; raw HTML passes through."""
    return re.sub(r'`([^`]+)`', lambda m: f'<code>{esc(m.group(1))}</code>', s)


LEAN_KEYWORDS = (
    'noncomputable|abbrev|def|structure|theorem|lemma|instance|where|'
    'let|fun|do|pure|match|with|if|then|else|deriving|variable|open|import')
LEAN_TYPES = r'Type|Prop|Nat|Bool|ℕ|ProbComp'

LEAN_TOKEN = re.compile(
    r'(?P<cm>--[^\n]*)'
    r'|(?P<kw>\b(?:' + LEAN_KEYWORDS + r')\b)'
    r'|(?P<ty>\b(?:' + LEAN_TYPES + r')\b)'
    r'|(?P<op>:=|=>|←|→|×|∑|•|≠|⟨|⟩|\$ᵗ)'
)


def hilean(code):
    """Lean syntax highlighting: emit HTML with span classes."""
    out, pos = [], 0
    for m in LEAN_TOKEN.finditer(code):
        out.append(esc(code[pos:m.start()]))
        kind = m.lastgroup
        out.append(f'<span class="{kind}">{esc(m.group())}</span>')
        pos = m.end()
    out.append(esc(code[pos:]))
    return ''.join(out)


def b64(path):
    with open(os.path.join(HERE, path), 'rb') as f:
        return base64.b64encode(f.read()).decode()


# All figure crops come from the same 200 dpi page render, so equal
# legibility means equal on-screen scale: width proportional to the PNG's
# intrinsic pixel width. Anchor: the Base MAC panel (1160 px) at 40vw.
FIG_SCALE = 40 / 1160  # vw per source pixel
FIG_MULT = 1.0  # global multiplier, set by the md's figscale directive


def png_width(path):
    import struct
    with open(os.path.join(HERE, path), 'rb') as f:
        head = f.read(24)
    return struct.unpack('>I', head[16:20])[0]


def parse_slides(text):
    text = re.sub(r'<!--(?!\s*(figwidth|codesize|figzoom)).*?-->', '', text, flags=re.S)
    return [s.strip() for s in re.split(r'\n---\n', text) if s.strip()]


def title_slide(block):
    title = subtitle = ''
    footer = []
    for line in block.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('## '):
            subtitle = line[3:]
        elif line.startswith('# '):
            title = line[2:]
        else:
            footer.append(line)
    foot = '<br>'.join(inline(l) for l in footer)
    return f'''
<section class="slide">
  <div style="margin:auto;text-align:center">
    <h1>{inline(title)}</h1>
    <p style="font-size:3.4vh;color:#374151;margin:.3em 0">{inline(subtitle)}</p>
    <p style="font-size:2.3vh;color:#6b7280">{foot}</p>
  </div>
</section>'''


def content_slide(block):
    lines = block.splitlines()
    title, img, alt, figwidth = '', None, '', 'max-content'
    codesize = None
    figzoom = 1.0
    blocks, bullets = [], []
    caption = None
    i = 0
    while i < len(lines):
        line = lines[i]
        s = line.strip()
        m = re.match(r'<!--\s*figwidth:\s*([0-9]+%)\s*-->', s)
        if m:
            figwidth = m.group(1)
        m2 = re.match(r'<!--\s*codesize:\s*([0-9.]+vh)\s*-->', s)
        if m2:
            codesize = m2.group(1)
        m3 = re.match(r'<!--\s*figzoom:\s*([0-9.]+)\s*-->', s)
        if m3:
            figzoom = float(m3.group(1))
        elif s.startswith('## '):
            title = s[3:]
        elif s.startswith('!['):
            m = re.match(r'!\[([^\]]*)\]\(([^)]+)\)', s)
            if m:
                alt, img = m.group(1), m.group(2)
        elif s.startswith('### '):
            caption = s[4:]
        elif s.startswith('**') and s.endswith('**'):
            caption = s[2:-2]
        elif s.startswith('```'):
            code = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('```'):
                code.append(lines[i])
                i += 1
            blocks.append((caption or '', '\n'.join(code)))
            caption = None
        elif s.startswith('- '):
            bullets.append(s[2:])
        i += 1

    # Bullets that BEGIN with a `backticked` fragment become hover tooltips
    # anchored at that fragment's occurrences in the slide's code; the rest
    # stay visible bullets. Anchors that match nothing fall back to bullets.
    tips, visible = [], []
    for b in bullets:
        m = re.match(r'`([^`]+)`', b)
        if m:
            tips.append((m.group(1), b))
        else:
            visible.append(b)

    # Anchor tips on the RAW code (before highlighting), so multi-token
    # anchors like `ProbComp (Key F n × Params G n)` match.
    tip_attrs = {}
    for idx, (anchor, text) in sorted(enumerate(tips), key=lambda t: -len(t[1][0])):
        pat = re.compile(r'(?<!\w)' + re.escape(anchor) + r"(?![\w'])")
        hit = False
        marked = []
        for cap, code in blocks:
            code2 = pat.sub(
                lambda m: f'@@TIP{idx}@@{m.group()}@@ENDTIP@@', code)
            hit = hit or code2 != code
            marked.append((cap, code2))
        if hit:
            blocks = marked
            tip_attrs[idx] = inline(text).replace('"', '&quot;')
            continue
        # No code hit: try anchoring inside the visible bullets' text.
        vhit = False
        for k, vb in enumerate(visible):
            vb2 = pat.sub(
                lambda m: f'@@TIP{idx}@@{m.group()}@@ENDTIP@@', vb)
            if vb2 != vb:
                visible[k] = vb2
                vhit = True
        if vhit:
            tip_attrs[idx] = inline(text).replace('"', '&quot;')
        else:
            visible.append(text)

    code_html = ''.join(
        f'<div class="proc"><div class="cap">{inline(cap)}</div><pre>{hilean(code)}</pre></div>'
        for cap, code in blocks)
    notes = ''
    if visible:
        lis = ''.join(f'<li>{inline(b)}</li>' for b in visible)
        notes = f'<ul class="notes">{lis}</ul>'

    for idx, attr in tip_attrs.items():
        start = f'<span class="tip" data-tip="{attr}">'
        code_html = code_html.replace(f'@@TIP{idx}@@', start)
        notes = notes.replace(f'@@TIP{idx}@@', start)
    code_html = code_html.replace('@@ENDTIP@@', '</span>')
    notes = notes.replace('@@ENDTIP@@', '</span>')
    fig = ''
    if img:
        w = png_width(img) * FIG_SCALE * FIG_MULT * figzoom
        fig = (f'<div class="figpane"><img style="width:{w:.2f}vw" '
               f'src="data:image/png;base64,{b64(img)}" alt="{esc(alt)}"></div>')
    csvar = f' --codesize:{codesize};' if codesize else ''
    return f'''
<section class="slide">
  <h2>{inline(title)}</h2>
  <div class="cols" style="grid-template-columns: {figwidth} auto;{csvar}">
    {fig}
    <div class="code">{code_html}{notes}</div>
  </div>
</section>'''


def main():
    global FIG_MULT
    text = open(MD).read()
    m = re.search(r'<!--\s*figscale:\s*([0-9.]+)\s*-->', text)
    if m:
        FIG_MULT = float(m.group(1))
    slides = parse_slides(text)
    body = title_slide(slides[0]) + ''.join(content_slide(s) for s in slides[1:])
    body = body.replace('<section class="slide">', '<section class="slide active">', 1)
    html = f'''<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>Formalizing KVAC in Lean</title>
<style>
  html,body {{ margin:0; height:100%; font-family: Helvetica, Arial, sans-serif; color:#111827; background:#e5e7eb; }}
  .slide {{ display:none; width:100vw; height:100vh; box-sizing:border-box; padding:2.2vh 2.5vw; background:#fff; flex-direction:column; }}
  .slide.active {{ display:flex; }}
  h1 {{ font-size:5.6vh; margin:.2em 0; }}
  h2 {{ font-size:3.8vh; margin:0 0 1.4vh 0; }}
  .cols {{ display:grid; gap:2%; flex:1; min-height:0; align-items:center; }}
  .figpane {{ min-width:0; }}
  .figpane img {{ max-width:100%; height:auto; display:block; margin:0 auto; border:1px solid #e5e7eb; border-radius:6px; }}
  .code {{ min-width:0; max-height:100%; overflow:auto; align-self:stretch; display:flex; flex-direction:column; justify-content:center; gap:1.4vh; }}
  .proc .cap {{ font-size:1.9vh; color:#6b7280; margin:1.8vh 0 .25vh 0; }}
  .proc:first-child .cap {{ margin-top:0; }}
  .proc pre {{ margin:0; font-size:var(--codesize, 1.5vh); line-height:1.35; background:#f8fafc; border:1px solid #e2e8f0; border-radius:6px; padding:.9vh 1vw; overflow-x:auto; }}
  .proc pre .kw {{ color:#7c3aed; font-weight:600; }}
  .proc pre .ty {{ color:#0f766e; }}
  .proc pre .op {{ color:#b45309; }}
  .proc pre .cm {{ color:#6b7280; font-style:italic; }}
  ul.notes {{ margin:.4vh 0 0 0; padding-left:1.3em; font-size:2.15vh; line-height:1.45; color:#1f2937; }}
  ul.notes li {{ margin-bottom:.7vh; }}
  ul.notes code {{ background:#f3f4f6; padding:.05em .3em; border-radius:4px; font-size:1.9vh; }}
  .proc .cap code {{ background:#f3f4f6; padding:.05em .3em; border-radius:4px; }}
  .footer {{ position:fixed; bottom:1.2vh; right:1.4vw; color:#9ca3af; font-size:1.8vh; }}
  .tip {{ text-decoration: underline dotted 2px #b45309; text-underline-offset: 3px; cursor: help; }}
  #tipbox {{ position:fixed; display:none; z-index:10; max-width:38vw; background:#111827; color:#f9fafb;
             font-size:1.95vh; line-height:1.45; padding:1.1vh 1vw; border-radius:8px;
             box-shadow:0 4px 18px rgba(0,0,0,.35); }}
  #tipbox code {{ background:#374151; color:#f9fafb; padding:.05em .3em; border-radius:4px; }}
</style></head><body>
{body}
<div class="footer"><span id="pg"></span> · ←/→</div>
<script>
  const s=[...document.querySelectorAll('.slide')];let i=0;
  const show=n=>{{i=Math.max(0,Math.min(s.length-1,n));s.forEach((e,j)=>e.classList.toggle('active',j===i));document.getElementById('pg').textContent=(i+1)+' / '+s.length;}};
  addEventListener('keydown',e=>{{if(e.key==='ArrowRight'||e.key===' ')show(i+1);if(e.key==='ArrowLeft')show(i-1);}});
  addEventListener('click',e=>{{if(!e.target.closest('a'))show(i+1)}});
  const h=parseInt(location.hash.slice(1)); show(isNaN(h)?0:h-1);
  const tb=document.createElement('div');tb.id='tipbox';document.body.appendChild(tb);
  document.querySelectorAll('.tip').forEach(el=>{{
    el.addEventListener('mouseenter',()=>{{
      tb.innerHTML=el.dataset.tip;tb.style.display='block';
      const r=el.getBoundingClientRect(),bw=tb.offsetWidth;
      let x=Math.min(r.left,innerWidth-bw-16);
      tb.style.left=Math.max(8,x)+'px';
      const below=r.bottom+8+tb.offsetHeight<innerHeight;
      tb.style.top=(below?r.bottom+8:r.top-tb.offsetHeight-8)+'px';
    }});
    el.addEventListener('mouseleave',()=>{{tb.style.display='none';}});
  }});
</script>
</body></html>'''
    open(OUT, 'w').write(html)
    print(f'wrote {OUT} ({len(html)} bytes, {len(slides)} slides)')


if __name__ == '__main__':
    sys.exit(main())
