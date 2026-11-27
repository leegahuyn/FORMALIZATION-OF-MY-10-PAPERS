import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Abel
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientCoverCohomology

/-! A contraction in every positive Čech degree for the actual point coefficient sheaf. -/

namespace ManuscriptAudit.PointCoefficientCoverHigherCohomology

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PointCoefficientExact ClosedSupportDetection
open scoped BigOperators

section Alternating

variable {I A : Type*} [AddCommGroup A]

private theorem first_face {n : ℕ} (i : I) (t : Fin (n+2) → I) :
    (Fin.cons i t) ∘ (0 : Fin (n+3)).succAbove = t := by
  funext j
  simp [Function.comp_def, Fin.succAbove_zero_apply]

private theorem remaining_face {n : ℕ} (i : I) (t : Fin (n+2) → I) (j : Fin (n+2)) :
    (Fin.cons i t) ∘ j.succ.succAbove = Fin.cons i (t ∘ j.succAbove) := by
  funext k
  refine Fin.cases ?_ (fun k => ?_) k
  · simp [Function.comp_def, Fin.succ_succAbove_zero]
  · simp [Function.comp_def, Fin.succ_succAbove_succ]

def alternating (n : ℕ) (c : (Fin (n+1) → I) → A) (t : Fin (n+2) → I) : A :=
  ∑ i : Fin (n+2), ((-1 : ℤ)^i.val) • c (t ∘ i.succAbove)

theorem contraction_identity (n : ℕ) (i : I) (c : (Fin (n+2) → I) → A)
    (t : Fin (n+2) → I) :
    alternating (n+1) c (Fin.cons i t) +
      alternating n (fun τ => c (Fin.cons i τ)) t = c t := by
  unfold alternating
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, pow_zero, one_zsmul, first_face, remaining_face,
    Fin.val_succ, pow_succ, mul_neg, mul_one, neg_smul, Finset.sum_neg_distrib]
  abel

theorem positive_cocycle_primitive (n : ℕ) (i : I) (c : (Fin (n+2) → I) → A)
    (hc : ∀ t, alternating (n+1) c t = 0) :
    alternating n (fun τ => c (Fin.cons i τ)) = c := by
  funext t
  have h := contraction_identity n i c t
  simpa only [hc, zero_add] using h

end Alternating

section ActualCover

variable {X : TopCat.{0}} (P : Set X) {I : Type*} (U : I → Opens X)
variable (M : P → AddCommGrpCat.{0})

abbrev VisibleAt (p : P) := {i : I // p.val ∈ U i}

abbrev InIntersection {n : ℕ} (t : Fin (n+1) → I) :=
  {p : P // ∀ j, p.val ∈ U (t j)}

/-- The ordinary Čech cochain values in tuple-intersection coordinates. -/
abbrev CoverCochain (n : ℕ) :=
  ∀ t : Fin (n+1) → I, ∀ p : InIntersection P U t, M p.val

def coverReindex (n : ℕ) :
    CoverCochain P U M n ≃+ (∀ p : P, (Fin (n+1) → VisibleAt P U p) → M p) where
  toFun c p t := c (fun j => (t j).val) ⟨p, fun j => (t j).property⟩
  invFun c t p := c p.val (fun j => ⟨t j, p.property j⟩)
  left_inv c := by
    funext t p
    rfl
  right_inv c := by
    funext p t
    rfl
  map_add' _ _ := rfl

def coverDifferential (n : ℕ) (c : CoverCochain P U M n) : CoverCochain P U M (n+1) :=
  fun t p => ∑ i : Fin (n+2), ((-1 : ℤ)^i.val) •
    c (t ∘ i.succAbove) ⟨p.val, fun j => p.property (i.succAbove j)⟩

theorem cover_differential_formula (n : ℕ) (c : CoverCochain P U M n)
    (t : Fin (n+2) → I) (p : InIntersection P U t) :
    coverDifferential P U M n c t p =
      ∑ i : Fin (n+2), ((-1 : ℤ)^i.val) •
        c (t ∘ i.succAbove) ⟨p.val, fun j => p.property (i.succAbove j)⟩ := rfl

private theorem coverReindex_differential (n : ℕ) (c : CoverCochain P U M n) :
    coverReindex P U M (n+1) (coverDifferential P U M n c) =
      fun p => alternating n (coverReindex P U M n c p) := rfl

set_option maxHeartbeats 1400000 in
theorem any_cover_positive_cocycle_is_coboundary (hCover : iSup U = ⊤) (n : ℕ)
    (c : CoverCochain P U M (n+1))
    (hc : coverDifferential P U M (n+1) c = 0) :
    ∃ a : CoverCochain P U M n, coverDifferential P U M n a = c := by
  classical
  have h (p : P) : ∃ i, p.val ∈ U i := by
    apply Opens.mem_iSup.mp
    rw [hCover]
    trivial
  let i (p : P) : VisibleAt P U p := ⟨Classical.choose (h p), Classical.choose_spec (h p)⟩
  let e := coverReindex P U M n
  let e' := coverReindex P U M (n+1)
  let a := e.symm (fun p t => e' c p (Fin.cons (i p) t))
  have hD := congrArg (coverReindex P U M (n+2)) hc
  rw [coverReindex_differential, map_zero] at hD
  refine ⟨a, e'.injective ?_⟩
  change coverReindex P U M (n+1) (coverDifferential P U M n a) = e' c
  rw [coverReindex_differential]
  funext p
  rw [show coverReindex P U M n a = (fun p t => e' c p (Fin.cons (i p) t)) from
    e.apply_symm_apply _]
  exact positive_cocycle_primitive n (i p) (e' c p)
    (fun t => congrFun (congrFun hD p) t)

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

theorem actual_cover_and_derived_positive_degrees (hCover : iSup U = ⊤) (n : ℕ) :
    (∀ c : CoverCochain P U M (n+1), coverDifferential P U M (n+1) c = 0 →
      ∃ a : CoverCochain P U M n, coverDifferential P U M n a = c) ∧
    Subsingleton ((coefficientSheaf P M).H (n+1)) :=
  ⟨any_cover_positive_cocycle_is_coboundary P U M hCover n,
    PointCoefficientAcyclic.H_succ_subsingleton P M n⟩

end ActualCover
end ManuscriptAudit.PointCoefficientCoverHigherCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientCoverHigherCohomology.contraction_identity,
      ``ManuscriptAudit.PointCoefficientCoverHigherCohomology.cover_differential_formula,
      ``ManuscriptAudit.PointCoefficientCoverHigherCohomology.any_cover_positive_cocycle_is_coboundary,
      ``ManuscriptAudit.PointCoefficientCoverHigherCohomology.actual_cover_and_derived_positive_degrees] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
