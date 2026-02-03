/-
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

In the statements and proofs, replace every \lambda to \eta.
-/

import MultivarIndepFormalize.Definitions
import MultivarIndepFormalize.DualSetMembershipSeparately

set_option linter.style.longLine false

open Real

noncomputable section

/-
**Lemma 3.2** `lem:Sn-membership`
"Something" is in S_Δ.

**Statement**
Let \(\Delta\ge2\) and \(1\le d_i\le \Delta\), \(1\le i\le \Delta\) be integers. Let \(\lambda_i,\mu_i\ge0\) for \(1\le i\le \Delta\). Then
\[
  \biggl(
  \prod_{i=1}^\Delta \frac{A_{d_i}(\lambda_i,\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\mu_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}},\,
  \prod_{i=1}^\Delta \frac{B_{d_i}(\lambda_i)^{\frac{1}{d_i}}}{A_{d_i+1}(\lambda_i,\mu_i)^{\frac{1}{d_i+1}}}
  \biggr) \in \calS_\Delta.
\]
-/
