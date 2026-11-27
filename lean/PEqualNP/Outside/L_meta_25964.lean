import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25964_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def circuit : Circuit :=
  ⟨[⟨GateOp.not, [5]⟩,
    ⟨GateOp.and, [0, 8]⟩,
    ⟨GateOp.or, [1, 2]⟩,
    ⟨GateOp.and, [1, 6]⟩,
    ⟨GateOp.or, [9, 11]⟩,
    ⟨GateOp.or, [4, 5]⟩,
    ⟨GateOp.and, [10, 13]⟩,
    ⟨GateOp.or, [12, 14]⟩], 15⟩

theorem fanInTwo : FanInTwo circuit := by
  intro g hg
  simp only [circuit, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_25964_aux

theorem PEqualNP.Outside.L_meta_25964 :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ 8 ∧ PEqualNP.NotBracket.notCount C ≤ 1 ∧
      PEqualNP.Represents.Represents
        (fun (u : Fin 4) (v : Fin 4) => (([13, 7, 3, 0] : List ℕ).getD u.val 0).testBit v.val) C := by
  exact ⟨PEqualNP.Outside.L_meta_25964_aux.circuit, PEqualNP.Outside.L_meta_25964_aux.fanInTwo,
    by decide, by decide, by decide +kernel⟩
