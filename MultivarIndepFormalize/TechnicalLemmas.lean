/-!
# Technical Lemmas (re-export)

This file re-exports the technical lemmas that were split into separate modules:
- `Concavity` — Lemma 3.1 (`A_d_pow_dinv_concave`)
- `BasicInequality` — Proposition 3.7 (`basic_ineq`)

Downstream files that previously imported `TechnicalLemmas` will continue to work
without changes.
-/

import MultivarIndepFormalize.Concavity
import MultivarIndepFormalize.BasicInequality
