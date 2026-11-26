import AuctionSep.Problem
import AuctionSep.BICWitness
import AuctionSep.DSICBound

namespace AuctionSep

/-- Prove `MainGoal` without `sorry`, without new `axiom`s, and without `native_decide`. -/
theorem main_theorem : MainGoal := by
  refine ⟨BICWitness.M_bic, 2324277 / 2621440,
    BICWitness.M_bic_feasible,
    BICWitness.M_bic_isBIC,
    BICWitness.M_bic_isInterimIR,
    ?_,
    DSICBound.dsic_expectedRevenue_le⟩
  rw [BICWitness.M_bic_expectedRevenue]
  norm_num

end AuctionSep
