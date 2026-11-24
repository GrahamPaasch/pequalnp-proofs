import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3451_1 (h1 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ k : Fin (N + N), (D.wires (List.ofFn (fun x : Fin (N + N) => decide (x = k)))).getD (N + N + j) false = false))
    (h2 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (∀ j < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ k : Fin (N + N), (C.wires (List.ofFn (fun x : Fin (N + N) => decide (x = k)))).getD (N + N + j) false = false) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ PEqualNP.MetaComplexity.circuitFun (N + N) D = PEqualNP.MetaComplexity.circuitFun (N + N) C ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ k k' : Fin (N + N), (k = k' ∨ ∃ p l : Fin N, ¬ I p l ∧ k = Fin.castAdd N p ∧ k' = Fin.natAdd N l) → (D.wires (List.ofFn (fun x : Fin (N + N) => decide (x = k ∨ x = k')))).getD (N + N + j) false = false)) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  intro N I _ C hI hM hR hF
  obtain ⟨D1, hM1, hR1, hs1, hF1, hot1⟩ := h1 N I C hI hM hR hF
  have hF1' : ∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D1 z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [hF1]
    exact hF z
  obtain ⟨D, hM2, hR2, hs2, hF2, hQ⟩ := h2 N I D1 hI hM1 hR1 hF1' hot1
  have hone : ∀ k : Fin (N + N),
      (fun x : Fin (N + N) => decide (x = k ∨ x = k)) = fun x : Fin (N + N) => decide (x = k) := by
    intro k
    funext x
    exact decide_eq_decide.mpr (or_self_iff)
  refine ⟨D, hM2, hR2, le_trans hs2 hs1, ?_, ?_, ?_⟩
  · intro z
    rw [hF2, hF1]
    exact hF z
  · intro j hj hand p0 l0 hn
    exact hQ j hj hand (Fin.castAdd N p0) (Fin.natAdd N l0) (Or.inr ⟨p0, l0, hn, rfl, rfl⟩)
  · intro j hj hand
    refine ⟨fun p => ?_, fun l => ?_⟩
    · have h := hQ j hj hand (Fin.castAdd N p) (Fin.castAdd N p) (Or.inl rfl)
      rw [hone] at h
      exact h
    · have h := hQ j hj hand (Fin.natAdd N l) (Fin.natAdd N l) (Or.inl rfl)
      rw [hone] at h
      exact h
