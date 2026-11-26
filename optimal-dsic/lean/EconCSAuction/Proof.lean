import EconCSAuction.Spec
import EconCSAuction.Lemma1
import EconCSAuction.Lemma2
import EconCSAuction.Lemma3
import EconCSAuction.Lemma4
import EconCSAuction.Lemma5
import EconCSAuction.Lemma5Sharp
import EconCSAuction.Theorem1
import EconCSAuction.Theorem2

/-!
# Top-level theorems

* `theorem1_proof : Theorem1Statement` — for every `L ≥ 2/π`, `flagshipMechanism L` is feasible,
  DSIC, ex-post IR, has the stated revenue, and is optimal among all feasible BIC + interim-IR and
  all feasible DSIC + ex-post IR mechanisms.
* `sharpThreshold_proof : SharpThresholdStatement` — the threshold `2/π` is exact.

Both statements are definitions in `EconCSAuction.Spec`, which contains no proofs.
-/

namespace EconCSAuction

/-- Top-level proof certifying `Theorem1Statement` from `EconCSAuction.Spec`. -/
theorem theorem1_proof : Theorem1Statement := theorem1_main

/-- The threshold `2/π` is exact. -/
theorem sharpThreshold_proof : SharpThresholdStatement := by
  intro L hL0
  refine ⟨⟨fun h => ?_, fun hL M hF hD hI => flagshipMechanism_optimal_DSIC hL M hF hD hI⟩,
    ⟨fun h => ?_, fun hL M hF hB hI => flagshipMechanism_optimal_BIC hL M hF hB hI⟩⟩
  · by_contra hlt
    obtain ⟨M, hF, hD, hI, _, _, hrev⟩ :=
      flagshipMechanism_suboptimal_below_two_div_pi hL0 (not_le.mp hlt)
    exact absurd (h M hF hD hI) (not_le.mpr hrev)
  · by_contra hlt
    obtain ⟨M, hF, hD, hI, _, _, hrev⟩ :=
      flagshipMechanism_suboptimal_below_two_div_pi hL0 (not_le.mp hlt)
    have hBI := dsic_exPostIR_implies_bic_interimIR hL0 hF hD hI
    exact absurd (h M hF hBI.1 hBI.2) (not_le.mpr hrev)

end EconCSAuction
