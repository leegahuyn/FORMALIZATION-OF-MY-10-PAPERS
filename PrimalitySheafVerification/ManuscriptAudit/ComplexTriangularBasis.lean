import Lean.Util.CollectAxioms
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Matrix.Block
import PrimalitySheafVerification.ManuscriptAudit.InvariantSubspaceMatrixBlocks

/-! Every endomorphism of a finite complex vector space has a triangular basis. -/

namespace ManuscriptAudit.ComplexTriangularBasis

open Module InvariantSubspaceMatrixBlocks

noncomputable section

private def onePlusEquiv (n : ℕ) : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (Sum.inl 0) Sum.inr
  left_inv i := by
    cases i with
    | inl i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        rfl
    | inr i => rfl
  right_inv i := Fin.cases rfl (fun _ => rfl) i

private def TriangularAt (n : ℕ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V],
    finrank ℂ V = n → ∀ T : Module.End ℂ V,
    ∃ b : Basis (Fin n) ℂ V, (LinearMap.toMatrix b b T).BlockTriangular id

private theorem triangularAt (n : ℕ) : TriangularAt n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro V _ _ _ hn T
    classical
    by_cases hn₀ : n = 0
    · have h0 : finrank ℂ V = 0 := hn.trans hn₀
      rw [hn₀]
      refine ⟨Module.finBasisOfFinrankEq ℂ V h0, ?_⟩
      exact fun i => Fin.elim0 i
    have hnPos : 0 < n := Nat.pos_of_ne_zero hn₀
    have hV : 0 < finrank ℂ V := by rwa [hn]
    letI : Nontrivial V := Module.finrank_pos_iff.mp hV
    obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
    obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
    let U : Submodule ℂ V := Submodule.span ℂ {v}
    have hU : finrank ℂ U = 1 := finrank_span_singleton hv.2
    have hInvariant (x : V) (hx : x ∈ U) : T x ∈ U := by
      obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp (show x ∈ Submodule.span ℂ {v} from hx)
      rw [map_smul, hv.apply_eq_smul]
      exact U.smul_mem _ (U.smul_mem _ (Submodule.mem_span_singleton_self v))
    let d := finrank ℂ (V ⧸ U)
    have hd : d + 1 = n := by
      simpa only [d, hU, hn] using U.finrank_quotient_add_finrank
    have hlt : d < n := by omega
    obtain ⟨q, hq⟩ := ih d hlt (V ⧸ U) rfl (quotientMap T hInvariant)
    obtain ⟨W, hW⟩ := U.exists_isCompl
    let u := Module.finBasisOfFinrankEq ℂ U hU
    let b := adaptedBasis hW u q
    let e : Fin 1 ⊕ Fin d ≃ Fin n := (onePlusEquiv d).trans (finCongr hd)
    let b' := b.reindex e
    have hEntry (i j : Fin 1 ⊕ Fin d) :
        LinearMap.toMatrix b' b' T (e i) (e j) = LinearMap.toMatrix b b T i j := by
      simp only [b', LinearMap.toMatrix_apply, Basis.reindex_apply, Basis.repr_reindex_apply,
        Equiv.symm_apply_apply]
    have hL (i : Fin 1) : (e (Sum.inl i)).val = 0 := rfl
    have hR (i : Fin d) : (e (Sum.inr i)).val = i.val + 1 := rfl
    refine ⟨b', ?_⟩
    intro i j hij
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    change (e j).val < (e i).val at hij
    rw [hEntry]
    cases i with
    | inl i =>
        rw [hL] at hij
        omega
    | inr i =>
        cases j with
        | inl j => exact adapted_lower_left hW T hInvariant u q j i
        | inr j =>
          rw [hR, hR] at hij
          rw [adapted_lower_right hW T hInvariant]
          exact hq (show j < i by omega)

theorem exists_triangular_basis (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (T : Module.End ℂ V) :
    ∃ b : Basis (Fin (finrank ℂ V)) ℂ V, (LinearMap.toMatrix b b T).BlockTriangular id :=
  triangularAt (finrank ℂ V) V rfl T

end
end ManuscriptAudit.ComplexTriangularBasis

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ComplexTriangularBasis.exists_triangular_basis
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
