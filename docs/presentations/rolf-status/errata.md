# Errata to O24 §5.3, found while constructing the Theorem 5.1 reduction

Companion note to the status presentation (2026-07-30). Paper: Orrù,
*Revisiting Keyed-Verification Anonymous Credentials*, IACR ePrint 2024/1552
("O24"), as `docs/Orru_2024.pdf`. Each item below is a discrepancy between the
paper's printed §5.3 material and what the reduction, worked in full detail,
actually requires. Every item is checkable by hand against the paper; none
weakens the result — the assumptions are the paper's own, and only the
additive constant changes (3/p → 5/p, both ≈ 2<sup>−250</sup> at
ristretto255).

## 1. The 1/p non-vanishing bound should be 3/p (p. 38)

The proof of Lemma 5.4 needs the affinely-substituted forgery polynomial to
stay nonzero. The paper (p. 38, after Eq. 16) asserts that the partial
evaluation ψ(χ) = ϕ(aₕ + χbₕ, a₀ + χb₀, …) "is still a non-zero polynomial
in ℤp[χ], of degree at most 3, except with probability 1/p".

The degree-3 claim is right; the probability constant is stated without
derivation and is too small. The bad event is that the hidden shift
(aₕ, a₀, aᵣ, a₁, a<sub>u,1</sub>, …) lands on a root of the nonzero
polynomial ϕ — in particular ψ ≡ 0 forces ψ(0) = ϕ(a⃗) = 0. And ϕ has total
degree 3: its top monomials come from
α<sub>v,j</sub>·uⱼ·(x₀+xᵣ+mⱼx₁)·(x₀+xᵣ+m*x₁), a degree-2 representation
term times the degree-1 key polynomial. Schwartz–Zippel over the uniform
shift therefore gives 3/p; a bare 1/p is the bound a degree-1 polynomial
would give.

## 3. Eq. 13: X₀'s X-coefficient (typo)

Eq. 13 defines the affine embedding of the public parameters off the 3-DL
instance (X, X′, X″). The paper prints X₀'s X-coefficient as
a<sub>h</sub>b₀ + b<sub>h</sub>. Expanding X₀ = x₀·H under the affine
substitution v ↦ a<sub>v</sub> + x·b<sub>v</sub> gives the X-coefficient

&nbsp;&nbsp;&nbsp;&nbsp;a₀b<sub>h</sub> + b₀a<sub>h</sub>,

i.e. the printed version drops the a₀ factor. The corrected coefficient is
documented at its use site in the reduction-core module under review
(PR #88, `AGMReduction/Core.lean`, docstring at the Eq. 13 embedding).

## 4. Eq. 14: signing-response coefficient (typo)

Eq. 14 gives the simulated signing response's coefficient. The paper prints
the factor as a·uⱼ·(a<sub>h</sub>a₀ + a<sub>h</sub> + mⱼa₁); the correct
factor is

&nbsp;&nbsp;&nbsp;&nbsp;A = a₀ + a<sub>r</sub> + a₁mⱼ,

the key polynomial's constant part evaluated at the queried message. Also
documented at its use site in PR #88.

## 6. Theorem 5.1's printed bound elides the gap-DL term

The printed bound is Adv<sup>3-dl</sup> + Adv<sup>dl</sup> + 3/p. The
paper's own proof of Lemma 5.5 case-splits on a collision event and sends the
collision branch to gap-DL via Claim 5.6 — so the assembled bound carries a
gap-DL advantage term that the printed theorem statement does not show. The
formalized target keeps it explicit:

&nbsp;&nbsp;&nbsp;&nbsp;Adv<sup>ufcmva</sup>(A) ≤ Adv<sup>3-dl</sup>(B₁) +
Adv<sup>gap-dl</sup>(B<sub>gap</sub>) + 5/p,

with 5/p = 3/p (item 1) + 1/p (the keygen-shear bad event x₁ = 0 in the
no-collision branch) + 1/p (the vanishing-denominator bad event in the
gap-DL branch). The paper's Adv<sup>dl</sup> term has no reduction behind it
in this proof plan; it survives only as nonnegative slack.

## Status

The corrections to Eqs. 13/14 are visible today in the open PR #88 diff
(module `AGMReduction/Core`); the remaining items are documented in the
reduction modules queued behind it, in the order shown on the
presentation's architecture slide. This note reports findings about the
paper; the formal-completion status of each module is tracked on the
project's blueprint page.
