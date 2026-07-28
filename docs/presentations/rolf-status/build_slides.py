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
    """Backticks to <code>, **…** to <b>; raw HTML passes through."""
    s = re.sub(r'`([^`]+)`', lambda m: f'<code>{esc(m.group(1))}</code>', s)
    return re.sub(r'\*\*([^*]+)\*\*', r'<b>\1</b>', s)


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
    text = re.sub(r'<!--(?!\s*(figwidth|codesize|figzoom|label)).*?-->', '', text, flags=re.S)
    return [s.strip() for s in re.split(r'\n---\n', text) if s.strip()]


def title_slide(block):
    title = subtitle = ''
    footer = []
    logo = ''
    for line in block.splitlines():
        line = line.strip()
        if not line:
            continue
        if line.startswith('## '):
            subtitle = line[3:]
        elif line.startswith('# '):
            title = line[2:]
        elif line.startswith('!['):
            m = re.match(r'!\[([^\]]*)\]\(([^)]+)\)', line)
            if m:
                logo = (f'<img src="data:image/png;base64,{b64(m.group(2))}" '
                        f'alt="{esc(m.group(1))}" '
                        'style="height:13vh;margin-bottom:4vh">')
        else:
            footer.append(line)
    foot = '<br>'.join(inline(l) for l in footer)
    return f'''
<section class="slide">
  <div style="margin:auto;text-align:center">
    {logo}
    <h1>{inline(title)}</h1>
    <p style="font-size:3.4vh;color:#374151;margin:.3em 0">{inline(subtitle)}</p>
    <p style="font-size:2.3vh;color:#6b7280">{foot}</p>
  </div>
</section>'''


def content_slide(block, nav=''):
    lines = block.splitlines()
    title, img, alt, figwidth = '', None, '', 'max-content'
    codesize = None
    figzoom = 1.0
    blocks, bullets = [], []
    caption = None
    prose = []

    def flush_prose():
        nonlocal caption
        while prose and not prose[-1].strip():
            prose.pop()
        if prose:
            blocks.append(('text', caption or '', '\n'.join(prose), None))
            caption = None
            prose.clear()

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
            flush_prose()
            title = s[3:]
        elif s.startswith('!['):
            flush_prose()
            m = re.match(r'!\[([^\]]*)\]\(([^)\s]+)(?:\s+"([^"]*)")?\)', s)
            if m and img is None:
                alt, img = m.group(1), m.group(2)
            elif m:
                # Later images render in-flow in the code column,
                # consuming the pending caption.
                blocks.append(('img', caption or '', m.group(2),
                               (m.group(1), m.group(3))))
                caption = None
        elif s.startswith('### '):
            flush_prose()
            caption = s[4:]
        elif s.startswith('**') and s.endswith('**'):
            flush_prose()
            caption = s[2:-2]
        elif s.startswith('```'):
            flush_prose()
            code = []
            i += 1
            while i < len(lines) and not lines[i].strip().startswith('```'):
                code.append(lines[i])
                i += 1
            blocks.append(('code', caption or '', '\n'.join(code), None))
            caption = None
        elif s.startswith('- '):
            flush_prose()
            sub = line.startswith('  ')
            bullets.append((s[2:], False, sub))
        elif s.startswith('> '):
            flush_prose()
            bullets.append((s[2:], True, False))
        elif s.startswith('<!--'):
            pass
        elif s:
            # Plain prose (e.g. a mathematical statement): renders in-flow
            # in the code column with line structure preserved.
            prose.append(line.rstrip())
        elif prose:
            prose.append('')
        i += 1
    flush_prose()

    # Bullets that BEGIN with a `backticked` fragment become hover tooltips
    # anchored at that fragment's occurrences in the slide's code; the rest
    # stay visible bullets. Anchors that match nothing fall back to bullets.
    tips, visible = [], []
    for b, small, sub in bullets:
        m = re.match(r'`([^`]+)`', b)
        if m and not sub:
            tips.append((m.group(1), b))
        else:
            visible.append((b, small, sub))

    # Anchor tips on the RAW code (before highlighting), so multi-token
    # anchors like `ProbComp (Key F n × Params G n)` match.
    tip_attrs = {}
    for idx, (anchor, text) in sorted(enumerate(tips), key=lambda t: -len(t[1][0])):
        pat = re.compile(r'(?<!\w)' + re.escape(anchor) + r"(?![\w'])")
        hit = False
        marked = []
        for kind, cap, code, extra in blocks:
            cap2 = pat.sub(
                lambda m: f'@@TIP{idx}@@{m.group()}@@ENDTIP@@', cap) if cap else cap
            hit = hit or cap2 != cap
            if kind not in ('code', 'text'):
                marked.append((kind, cap2, code, extra))
                continue
            code2 = pat.sub(
                lambda m: f'@@TIP{idx}@@{m.group()}@@ENDTIP@@', code)
            hit = hit or code2 != code
            marked.append((kind, cap2, code2, extra))
        if hit:
            blocks = marked
            tip_attrs[idx] = inline(text).replace('"', '&quot;')
            continue
        # No code hit: try anchoring inside the visible bullets' text.
        vhit = False
        for k, (vb, small, sub) in enumerate(visible):
            vb2 = pat.sub(
                lambda m: f'@@TIP{idx}@@{m.group()}@@ENDTIP@@', vb)
            if vb2 != vb:
                visible[k] = (vb2, small, sub)
                vhit = True
        if vhit:
            tip_attrs[idx] = inline(text).replace('"', '&quot;')
        else:
            visible.append((text, False, False))

    def render_block(kind, cap, code, extra):
        capdiv = f'<div class="cap">{inline(cap)}</div>' if cap else ''
        if kind == 'img':
            alt2, accent = extra
            w = png_width(code) * FIG_SCALE * FIG_MULT * figzoom
            astyle = (f'border-left:0.55vh solid {accent};padding-left:0.6vw;'
                      if accent else '')
            return (f'<div class="proc">{capdiv}'
                    f'<div class="inlinefig" style="{astyle}">'
                    f'<img style="width:{w:.2f}vw" '
                    f'src="data:image/png;base64,{b64(code)}" alt="{esc(alt2)}"></div></div>')
        if kind == 'text':
            return (f'<div class="proc">{capdiv}'
                    f'<div class="mathtext">{inline(code)}</div></div>')
        return f'<div class="proc">{capdiv}<pre>{hilean(code)}</pre></div>'

    code_html = ''.join(render_block(*b) for b in blocks)
    notes = ''
    if visible:
        items = []
        for b, small, sub in visible:
            li = (f'<li class="fine">{inline(b)}</li>' if small
                  else f'<li>{inline(b)}</li>')
            if sub and items:
                prev = items[-1]
                if prev.endswith('</ul></li>'):
                    items[-1] = prev[:-len('</ul></li>')] + li + '</ul></li>'
                else:
                    items[-1] = prev[:-len('</li>')] + '<ul class="subnotes">' + li + '</ul></li>'
            else:
                items.append(li)
        notes = f'<ul class="notes">{"".join(items)}</ul>'

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
  <div class="titlerow"><h2>{inline(title)}</h2>{nav}</div>
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

    # Symbolic slide labels: `<!-- label: name -->` names a slide, and
    # `href="#name"` anywhere in the md resolves to that slide's number at
    # build time, so slides can move without link rewrites.
    labels = {}
    for i, s in enumerate(slides):
        for m in re.finditer(r'<!--\s*label:\s*([\w-]+)\s*-->', s):
            labels[m.group(1)] = i + 1

    def resolve(m):
        name = m.group(1)
        if name not in labels:
            sys.exit(f'unknown slide label in link: #{name}')
        return f'href="#{labels[name]}"'
    slides = [re.sub(r'href="#([a-zA-Z][\w-]*)"', resolve, s) for s in slides]

    # Per-slide navigation: a link to the slide's box (first slide sharing
    # the title prefix before " · ") and to the overview (the first content
    # slide, whose title has no box prefix).
    titles = []
    for s in slides[1:]:
        t = next((l.strip()[3:] for l in s.splitlines()
                  if l.strip().startswith('## ')), '')
        titles.append(t)
    overview_no = 2
    box_first = {}
    for i, t in enumerate(titles):
        if ' · ' in t:
            box = t.split(' · ')[0]
            box_first.setdefault(box, i + 2)

    rendered = []
    for i, s in enumerate(slides[1:]):
        no = i + 2
        links = []
        if no == overview_no:
            rendered.append(content_slide(s, ''))
            continue
        links.append(f'<a href="#{overview_no}">μCMZ</a>')
        for box, first in sorted(box_first.items(), key=lambda kv: kv[1]):
            if first != no:
                links.append(f'<a href="#{first}">{box}</a>')
        nav = f'<div class="slidenav">{" ".join(links)}</div>' if links else ''
        rendered.append(content_slide(s, nav))
    body = title_slide(slides[0]) + ''.join(rendered)
    body = body.replace('<section class="slide">', '<section class="slide active">', 1)
    html = f'''<!DOCTYPE html>
<html lang="en"><head><meta charset="utf-8">
<title>Formalizing KVAC in Lean</title>
<style>
  html,body {{ margin:0; height:100%; font-family: Helvetica, Arial, sans-serif; color:#111827; background:#e5e7eb; }}
  .slide {{ display:none; position:relative; width:100vw; height:100vh; box-sizing:border-box; padding:2.2vh 2.5vw; background:#fff; flex-direction:column; }}
  .slide.active {{ display:flex; }}
  h1 {{ font-size:5.6vh; margin:.2em 0; }}
  h2 {{ font-size:3.8vh; margin:0; }}
  .titlerow {{ display:flex; align-items:flex-start; gap:2vw; margin-bottom:1.4vh; }}
  .titlerow h2 {{ flex:1 1 auto; min-width:0; }}
  .cols {{ display:grid; gap:2%; flex:1; min-height:0; align-items:center; }}
  .figpane {{ min-width:0; }}
  .inlinefig img {{ max-width:100%; display:block; border:1px solid #e5e7eb; border-radius:6px; }}
  .figpane img {{ max-width:100%; height:auto; display:block; margin:0 auto; border:1px solid #e5e7eb; border-radius:6px; }}
  .code {{ min-width:0; max-height:100%; overflow:auto; align-self:stretch; display:flex; flex-direction:column; justify-content:center; gap:1.4vh; }}
  .proc .cap {{ font-size:1.9vh; color:#6b7280; margin:1.8vh 0 .25vh 0; }}
  .proc:first-child .cap {{ margin-top:0; }}
  .proc pre {{ margin:0; font-size:var(--codesize, 1.5vh); line-height:1.35; background:#f8fafc; border:1px solid #e2e8f0; border-radius:6px; padding:.9vh 1vw; overflow-x:auto; }}
  .proc pre .kw {{ color:#7c3aed; font-weight:600; }}
  .proc pre .ty {{ color:#0f766e; }}
  .proc pre .op {{ color:#b45309; }}
  .proc pre .cm {{ color:#6b7280; font-style:italic; }}
  .proc .mathtext {{ white-space:pre-wrap; font-size:2.0vh; line-height:1.5; color:#1f2937;
                     background:#f8fafc; border:1px solid #e2e8f0; border-radius:6px; padding:.9vh 1vw; }}
  ul.notes {{ margin:.4vh 0 0 0; padding-left:1.3em; font-size:2.15vh; line-height:1.45; color:#1f2937; }}
  ul.notes li {{ margin-bottom:.7vh; }}
  ul.subnotes {{ margin:.5vh 0 0 0; padding-left:1.2em; }}
  ul.subnotes li {{ font-size:1.85vh; color:#374151; margin-bottom:.3vh; }}
  ul.notes li.fine {{ font-size:1.25vh; color:#4b5563; line-height:1.4; list-style:none; margin-left:-1.3em; }}
  ul.notes li + li.fine:not(li.fine + li.fine) {{ margin-top:2.2vh; }}
  ul.notes li.fine code {{ font-size:1.15vh; }}
  ul.notes code {{ background:#f3f4f6; padding:.05em .3em; border-radius:4px; font-size:1.9vh; }}
  .proc .cap code {{ background:#f3f4f6; padding:.05em .3em; border-radius:4px; }}
  .figpane img, .inlinefig img {{ cursor: zoom-in; }}
  #lightbox {{ position:fixed; inset:0; display:none; z-index:50; background:rgba(17,24,39,.88);
               align-items:center; justify-content:center; cursor:zoom-out; }}
  #lightbox.open {{ display:flex; }}
  #lightbox img {{ max-width:94vw; max-height:94vh; background:#fff; border-radius:8px;
                   box-shadow:0 8px 40px rgba(0,0,0,.5); }}
  .slidenav {{ flex:0 0 auto; white-space:nowrap; margin-top:1.2vh; font-size:2vh; }}
  .slidenav a {{ color:#6b7280; text-decoration:none; border-bottom:1px dotted #9ca3af; margin-left:1.2vw; }}
  .slidenav a:hover {{ color:#111827; }}
  .footer {{ position:fixed; bottom:1.2vh; right:1.4vw; color:#9ca3af; font-size:1.8vh; }}
  .marklogo {{ position:fixed; bottom:1.2vh; left:1.4vw; height:4.5vh; z-index:5; }}
  .footer a {{ cursor:pointer; color:#6b7280; }}
  .footer a:hover {{ color:#111827; }}
  .tip {{ text-decoration: underline dotted 2px #b45309; text-underline-offset: 3px; cursor: help; }}
  #tipbox {{ position:fixed; display:none; z-index:10; max-width:38vw; background:#111827; color:#f9fafb;
             font-size:1.95vh; line-height:1.45; padding:1.1vh 1vw; border-radius:8px;
             box-shadow:0 4px 18px rgba(0,0,0,.35); }}
  #tipbox code {{ background:#374151; color:#f9fafb; padding:.05em .3em; border-radius:4px; }}
</style></head><body>
{body}
<img class="marklogo" src="data:image/png;base64,{b64('assets/mark/png/baif-agent-mark-black.png')}" alt="Beneficial AI Foundation agent mark">
<div class="footer"><span id="pg"></span> · <a id="prevA" title="previous slide">←</a>/<a id="nextA" title="next slide">→</a></div>
<script>
  const s=[...document.querySelectorAll('.slide')];let i=0;
  const show=n=>{{i=Math.max(0,Math.min(s.length-1,n));s.forEach((e,j)=>e.classList.toggle('active',j===i));document.getElementById('pg').textContent=(i+1)+' / '+s.length;const ml=document.querySelector('.marklogo');if(ml)ml.style.display=i===0?'none':'block';history.replaceState(null,'','#'+(i+1));}};
  addEventListener('keydown',e=>{{if(e.key==='ArrowRight'||e.key===' ')show(i+1);if(e.key==='ArrowLeft')show(i-1);}});
  document.getElementById('prevA').addEventListener('click',()=>show(i-1));
  document.getElementById('nextA').addEventListener('click',()=>show(i+1));
  let wheelAt=0;
  addEventListener('wheel',e=>{{
    const c=e.target.closest('.code');
    if(c&&c.scrollHeight>c.clientHeight)return;   // let long columns scroll
    const now=Date.now();
    if(now-wheelAt<450||Math.abs(e.deltaY)<12)return;
    wheelAt=now;
    show(e.deltaY>0?i+1:i-1);
  }},{{passive:true}});
  addEventListener('click',e=>{{if(!e.target.closest('a'))show(i+1)}});
  const goHash=()=>{{const h=parseInt(location.hash.slice(1)); if(!isNaN(h))show(h-1);}};
  addEventListener('hashchange',goHash);
  const h=parseInt(location.hash.slice(1)); show(isNaN(h)?0:h-1);
  const lb=document.createElement('div');lb.id='lightbox';lb.innerHTML='<img>';document.body.appendChild(lb);
  const lbimg=lb.querySelector('img');
  document.querySelectorAll('.figpane img, .inlinefig img').forEach(im=>{{
    im.addEventListener('click',e=>{{e.stopPropagation();lbimg.src=im.src;lbimg.alt=im.alt;lb.classList.add('open');}});
  }});
  lb.addEventListener('click',e=>{{e.stopPropagation();lb.classList.remove('open');}});
  addEventListener('keydown',e=>{{if(e.key==='Escape')lb.classList.remove('open');}});
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
