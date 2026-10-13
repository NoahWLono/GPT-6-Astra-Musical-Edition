# Focused prior-art comparison: positive bounded-norm golden progressions

Audit date: 13 October 2026. This is a targeted comparison, not a certification
of novelty. The Lean theorem establishes correctness within its stated class;
it does not establish originality or solve global tuning optimization.

## Result being compared
For S_B = {x > 0 in Z[phi] : |N(x)| <= B}, integer B >= 64, the exact maximum
number of terms is floor((-M+sqrt(5M²+4B))/2)+ceil(M phi), where
M = max{m >= 0 : floor(5m²/4) <= B}. Every maximizing common difference has
absolute norm one. Positivity is essential to the sharp constant 1+sqrt(2).
The first step is a quadratic-polynomial bound; boundedness alone is not novel.

## Primary sources inspected

1. Dettmann–Taylor-West, Algebraic tunings, author manuscript, scale examples and
conclusion. https://people.maths.bris.ac.uk/~macpd/music/Algebraic_tunings.pdf
DOI https://doi.org/10.1080/17459737.2023.2234126
The norm-scale construction and additive musical motivation come from this
paper. Its conclusion suggests optimizing additive behavior at fixed scale
size, without specifying the single extremal objective used here. Its nine-note
illustration is not stated to be longest. The exact threshold formula and
maximizer rigidity theorem were not found in the inspected manuscript.

2. Dombek–Hajdu–Pethő, Representing algebraic integers as linear combinations of
units, author manuscript, Theorem 2.2 and its proof (manuscript pages 4, 7–8).
https://arato.inf.unideb.hu/petho.attila/cikkek/dhpnew6rev.pdf
They already prove an effectively computable AP-length bound for fixed-fold sums
of algebraic integers with bounded absolute norm in any number field. Taking
one summand and restricting to the positive golden embedding includes our
comparison class. Their proof uses finitely many unit-associate representatives
and a general multiplicative-group progression theorem. It does not give the
exact golden floor/ceiling maximum or characterize extremizing steps. Thus
existence of a bound must be credited to this prior work. Their quoted
Hajdu–Luca numerical bound should be read with the later corrigendum below.

3. Hajdu–Luca, On the length of arithmetic progressions in linear combinations
of S-units, Arch. Math. 94 (2010), 357–363, Theorem 1.1 and setup.
https://math.unideb.hu/sites/default/files/inline-files/hajdulucaaritprogrrev.pdf
Corrigendum, Arch. Math. 103 (2014), 399–400, complete two-page text inspected:
https://math.unideb.hu/sites/default/files/inline-files/corrigendum_rev.pdf
DOI https://doi.org/10.1007/s00013-014-0681-x
The original provides a general explicit AP upper bound in finite linear
combinations from finite-rank multiplicative groups. The corrigendum corrects
the nondegenerate-equation estimate and enlarges the final bound; it does not
withdraw finiteness. Neither inspected statement supplies an exact bounded-norm
golden maximum, a sharp sqrt(B) constant, or unit-step rigidity of maximizers.
Our elementary norm/interpolation proof does not depend on either version.

4. Bérczes–Hajdu–Pethő, Arithmetic progressions in the solution sets of norm form
equations, author manuscript, Theorems 2.1–2.4 and proof of 2.4 inspected.
https://math.unideb.hu/sites/default/files/inline-files/normarithcoord_revised.pdf
DOI https://doi.org/10.1216/RMJ-2010-40-2-383
The paper treats coordinate progressions on fixed norm equations, and algebraic
APs whose terms have the same signed field norm. The latter have length at most
the field degree. This is distinct from allowing every signed norm in [-B,B].
No exact formula or extremizing-step characterization for our class was found.
A contextual remark about all unit APs omits a low-degree qualification visible
in Newman's abstract; do not repeat it as a theorem for quadratic fields.

5. Elsholtz–Frei, Arithmetic progressions in binary quadratic forms and norm
forms, abstract and theorem scope inspected.
https://arxiv.org/abs/1810.11251
DOI https://doi.org/10.1112/blms.12256
The progression consists of represented rational-integer norm values, rather
than algebraic integers themselves. This does not subsume our extremal problem.

## Search coverage and limits
Queries covered “arithmetic progressions bounded norm quadratic integers”,
“longest arithmetic progression norm golden”, “quadratic integers units bound”,
“norm strips arithmetic progressions quadratic”, “norm-bounded progressions”,
and named-author/title citation chains. These yielded the general boundedness
literature above but no matching exact formula. Search results about Gowers
norms, represented norm values, or ideal norms were excluded as different
problems. Search absence is not evidence strong enough to certify novelty.

Newman's 1974 AMS original PDF could not be fetched in this pass. Its original
institutional publication abstract states a degree-at-least-four hypothesis:
https://www.govinfo.gov/content/pkg/GOVPUB-C13-53e2baf75c983ff7be000cbc8c650ad3/pdf/GOVPUB-C13-53e2baf75c983ff7be000cbc8c650ad3.pdf
No claim about its complete low-degree classification is made here.

## Remaining novelty questions
- Is the same extremal result known under indefinite binary quadratic
  inequalities, lattice chords in hyperbolic regions, or consecutive algebraic
  integers, without tuning terminology?
- Is the positivity-sharp constant 1+sqrt(2) already tabulated as a discrete
  quadratic minimax fact? The interpolation ingredient itself is elementary.
- Do unpublished notes or later citations of the bounded-norm/unit-AP papers
  contain the exact golden threshold calculation or eventual unit-step theorem?
- The threshold 64 is sufficient, not claimed minimal. Small-budget exceptions,
  all normalized maximizing lines, and the general real quadratic-order
  extension remain separate possible refinements.

Recommended wording: “a checked exact formula in a specified golden norm-scale
problem, with novelty still under review.” Do not say the published global
optimal-tuning question has been solved.

## Final indefinite-form / lattice-strip pass

Additional exact queries, completed 13 October 2026:
- “indefinite quadratic form” “arithmetic progression” bound length
- “quadratic” “lattice” “longest arithmetic progression”
- “hyperbola” “arithmetic progressions” lattice
- “bounded norm” “unit” “progressions” quadratic
- “indefinite binary quadratic” “progressions”
- “lattice strip” “arithmetic progression” quadratic
- “quadratic inequality” “arithmetic progression” maximum
- “norm” “unit step” “arithmetic progression”
- “lattice” “hyperbolic” “arithmetic progressions” longest
- “bounded” “indefinite quadratic form” “arithmetic progressions”

Additional primary material inspected:

6. Pethő–Ziegler, Arithmetic progressions on Pell equations, author manuscript,
introduction, Theorem 1, Corollary 1, and concluding questions.
https://arato.inf.unideb.hu/petho.attila/cikkek/Pell_v7.pdf
Its progressions are in one coordinate of integral solutions to a fixed Pell
equation X²-dY²=m. It gives explicit coordinate and length bounds and discusses
possible uniform bounds across these curves. The other coordinate need not
be an AP. This does not give the maximum for algebraic integers in a union of
norm levels, nor the golden threshold formula or eventual unit-step rigidity.

7. Ciss–Moody, Arithmetic Progressions on Conics, NIST-hosted paper,
abstract, introduction, and the scope of the hyperbola/conic constructions.
https://tsapps.nist.gov/publication/get_pdf.cfm?pub_id=922948
Its objects are rational points on conics with one coordinate in AP. Its
unit-hyperbola terminology refers to the curve x²-y²=1, not an algebraic unit
common difference. It provides constructions in a different comparison class.
No matching exact golden theorem appears in the inspected material.

The indefinite-form queries also found work on class-number sums over
discriminants in AP (Hashimoto, https://arxiv.org/abs/1003.3716), which was
excluded after reading its abstract because the AP parameter is the
discriminant. Results on geodesic lengths, represented norm values, divisor
hyperbolas, and geometric-progression-free sets likewise concern different
objects. No matching extremal lattice-strip theorem was located in this pass.

Unresolved access/coverage gaps: the AMS Newman original PDF returned an error;
its abstract and later citations do not replace a complete reading. Earlier
publisher access for Dombek–Hajdu–Pethő was unavailable, so comparison uses the
complete author manuscript. No comprehensive MathSciNet/zbMATH citation-index
review or exhaustive older geometry-of-numbers literature audit was performed.
No authors were contacted. The absence of a matching search result does not
exclude an equivalent unpublished or differently phrased theorem.
