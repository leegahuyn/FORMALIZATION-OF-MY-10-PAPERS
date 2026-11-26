import Lean.Util.CollectAxioms
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Tactic.Ring
import PrimalitySheafVerification.ManuscriptAudit.CuspDelta
import PrimalitySheafVerification.ManuscriptAudit.NodalConductor

/-! The equation y² = x²(x + 1) presents the affine nodal coordinate ring. -/

namespace ManuscriptAudit.NodalAffinePresentation

open Polynomial NodalConductor

noncomputable section

variable (K : Type*) [Field K]

def equation : K[X][X] :=
  X ^ 2 - C (((X : K[X]) ^ 2) * (X + 1))

def nodeX : coordinates K := ⟨x K, Algebra.subset_adjoin (by simp)⟩
def nodeY : coordinates K := ⟨y K, Algebra.subset_adjoin (by simp)⟩

private def baseMap : K[X] →ₐ[K] coordinates K := Polynomial.aeval (nodeX K)

private theorem equation_eval : (equation K).eval₂ (baseMap K).toRingHom (nodeY K) = 0 := by
  simp only [equation, eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, map_mul, map_add,
    map_one, map_pow, baseMap, aeval_X]
  apply Subtype.ext
  change y K ^ 2 - x K ^ 2 * (x K + 1) = 0
  unfold y x
  ring

def parameter : AdjoinRoot (equation K) →ₐ[K] coordinates K :=
  AdjoinRoot.liftAlgHom (equation K) (baseMap K) (nodeY K) (equation_eval K)

theorem parameter_base (f : K[X]) :
    parameter K (AdjoinRoot.of (equation K) f) = baseMap K f :=
  AdjoinRoot.liftAlgHom_of (equation K) (baseMap K) (nodeY K) (equation_eval K) f

theorem parameter_root : parameter K (AdjoinRoot.root (equation K)) = nodeY K :=
  AdjoinRoot.liftAlgHom_root (equation K) (baseMap K) (nodeY K) (equation_eval K)

private theorem parameter_mk (f : K[X][X]) :
    parameter K (AdjoinRoot.mk (equation K) f) =
      f.eval₂ (baseMap K).toRingHom (nodeY K) :=
  AdjoinRoot.liftAlgHom_mk (equation K) (baseMap K) (nodeY K) (equation_eval K) f

private theorem parameter_surjective : Function.Surjective (parameter K) := by
  let F := (coordinates K).val.comp (parameter K)
  have hx : x K ∈ F.range := by
    refine ⟨AdjoinRoot.of (equation K) X, ?_⟩
    change (parameter K (AdjoinRoot.of (equation K) X)).val = x K
    simp only [parameter_base, baseMap, aeval_X] <;> rfl
  have hy : y K ∈ F.range := by
    refine ⟨AdjoinRoot.root (equation K), ?_⟩
    change (parameter K (AdjoinRoot.root (equation K))).val = y K
    rw [parameter_root]
    rfl
  have hle : coordinates K ≤ F.range := by
    apply Algebra.adjoin_le
    intro g hg
    have hg' : g = x K ∨ g = y K := by simpa using hg
    rcases hg' with rfl | rfl
    · exact hx
    · exact hy
  intro z
  obtain ⟨q, hq⟩ := hle z.property
  exact ⟨q, Subtype.ext hq⟩

private def shift : K[X] →ₐ[K] K[X] := Polynomial.aeval (X - 1)

private theorem shift_injective : Function.Injective (shift K) := by
  let t : K[X] →ₐ[K] K[X] := Polynomial.aeval (X + 1)
  have e : t.comp (shift K) = AlgHom.id K K[X] := by
    apply Polynomial.algHom_ext
    simp [t, shift]
  exact Function.LeftInverse.injective (fun f =>
    congrArg (fun a : K[X] →ₐ[K] K[X] => a f) e)

private theorem base_value (f : K[X]) :
    (baseMap K f).val = expand K 2 (shift K f) := by
  have e : (coordinates K).val.comp (baseMap K) = (expand K 2).comp (shift K) := by
    apply Polynomial.algHom_ext
    simp [baseMap, shift, nodeX, x, Polynomial.expand_X]
  exact AlgHom.congr_fun e f

private theorem shifted_linear_eq_zero (a b : K[X])
    (h : (baseMap K a).val + (baseMap K b).val * y K = 0) :
    a = 0 ∧ b = 0 := by
  rw [base_value, base_value] at h
  have h₂ : expand K 2 (X * shift K a) +
      expand K 2 (shift K b * (X - 1)) * X ^ 3 = 0 := by
    calc
      _ = X ^ 2 * (expand K 2 (shift K a) + expand K 2 (shift K b) * y K) := by
        simp only [map_mul, map_sub, map_one, Polynomial.expand_X, y, x]
        ring
      _ = 0 := by rw [h, mul_zero]
  obtain ⟨ha, hb⟩ := CuspDelta.cusp_expanded_linear_eq_zero K _ _ h₂
  have hX : (X : K[X]) - 1 ≠ 0 := by
    intro e
    have h := congrArg constantCoeff e
    simpa using h
  constructor
  · apply shift_injective K
    rw [map_zero]
    exact (mul_eq_zero.mp ha).resolve_left X_ne_zero
  · apply shift_injective K
    rw [map_zero]
    exact (mul_eq_zero.mp hb).resolve_right hX

private theorem parameter_injective : Function.Injective (parameter K) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective q
  let r := f %ₘ equation K
  have hm : (equation K).Monic := Polynomial.monic_X_pow_sub_C _ (n := 2) (by decide)
  have hd : (equation K).natDegree = 2 := Polynomial.natDegree_X_pow_sub_C
  have hn : equation K ≠ 1 := by
    intro e
    have h := congrArg natDegree e
    rw [hd, natDegree_one] at h
    exact (by decide : (2 : ℕ) ≠ 0) h
  have hr : r.natDegree < 2 := by
    simpa only [hd] using Polynomial.natDegree_modByMonic_lt f hm hn
  have hlin : r = C (r.coeff 1) * X + C (r.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one (Nat.le_of_lt_succ hr)
  have hrem : r.eval₂ (baseMap K).toRingHom (nodeY K) = 0 :=
    (Polynomial.eval₂_modByMonic_eq_self_of_root (p := f) (equation_eval K)).trans
      ((parameter_mk K f).symm.trans hq)
  have heval : baseMap K (r.coeff 1) * nodeY K + baseMap K (r.coeff 0) = 0 := by
    rw [hlin] at hrem
    simpa only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X] using hrem
  have hsplit :
      (baseMap K (r.coeff 0)).val + (baseMap K (r.coeff 1)).val * y K = 0 := by
    have hyp := congrArg (coordinates K).val heval
    simpa only [map_add, map_mul, map_zero, nodeY, add_comm] using hyp
  obtain ⟨h0, h1⟩ := shifted_linear_eq_zero K _ _ hsplit
  have hzero : r = 0 := hlin.trans (by simp only [h0, h1, map_zero, zero_mul, zero_add])
  exact AdjoinRoot.mk_eq_zero.mpr ((Polynomial.modByMonic_eq_zero_iff_dvd hm).mp hzero)

/-- The actual affine equation is the subring obtained by the normalization parametrization. -/
def coordinateEquiv : AdjoinRoot (equation K) ≃ₐ[K] coordinates K :=
  AlgEquiv.ofBijective (parameter K) ⟨parameter_injective K, parameter_surjective K⟩

end
end ManuscriptAudit.NodalAffinePresentation

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.NodalAffinePresentation.coordinateEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
