import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import PrimalitySheafVerification.ManuscriptAudit.SpecIntExactDetection
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenDerivedComparison

/-!
# Exact-support infima for genuine two-open covers

The native sheaf gluing pullback identifies the two-open equalizer in
degree zero. With exact-support classification this suffices to compare
the two infima in Paper 6, physical p. 200, Definition 7.1.
-/

namespace ManuscriptAudit.SpecIntCechDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ExactSupportDetection
open ManuscriptAudit.TwoOpenDerivedComparison

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private abbrev G := AddCommGrpCat.{0}
private abbrev X := TopCat.of (PrimeSpectrum ℤ)

local instance (S : TopCat.{0}) : HasExt.{0} (AbelianSheaf S) :=
  IsGrothendieckAbelian.hasExt _

private def topIsTerminal (S : TopCat.{0}) : IsTerminal (⊤ : Opens S) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- The degree-zero group of the genuine two-open complex is actual H⁰. -/
def twoOpenH0Equiv {S : TopCat.{0}} (F : AbelianSheaf S) (U V : Opens S)
    (hCover : U ⊔ V = ⊤) : F.H 0 ≃ (twoOpenDifferential F.obj U V).ker := by
  let C := TopCat.Sheaf.interUnionPullbackCone (show TopCat.Sheaf G S from F) U V
  let T := CategoryTheory.forget G
  let h := TopCat.Sheaf.isLimitPullbackCone (show TopCat.Sheaf G S from F) U V
  let hType := (C.isLimitMapConeEquiv T).toFun (isLimitOfPreserves T h)
  let e : F.obj.obj (op (U ⊔ V)) ≃
      {z : F.obj.obj (op U) × F.obj.obj (op V) //
        F.obj.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op z.1 =
          F.obj.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op z.2} :=
    PullbackCone.IsLimit.equivPullbackObj hType
  let e' : F.obj.obj (op (U ⊔ V)) ≃ (twoOpenDifferential F.obj U V).ker :=
    e.trans (Equiv.subtypeEquivRight fun _ => sub_eq_zero.symm)
  refine (Sheaf.H.equiv₀ F (topIsTerminal S)).toEquiv.trans ?_
  rw [← hCover]
  exact e'

private abbrev group {S : TopCat.{0}} (F : AbelianSheaf S) (U V : Opens S) : ℕ → Type
  | 0 => (twoOpenDifferential F.obj U V).ker
  | 1 => (F.obj.obj (op (U ⊓ V))) ⧸ (twoOpenDifferential F.obj U V).range
  | _ => PUnit

/-- The exact-support infimum computed by the genuine two-open complex. -/
def fixedCechDetectionIndex (U V : Opens X) (P : Set X) : ℕ∞ :=
  sInf {i | ∃ n : ℕ, (n : ℕ∞) = i ∧
    ∃ F : AbelianSheaf X, stalkSupport F = P ∧ Nontrivial (group F U V n)}

private theorem exists_H0_witness {P : Set X} (h : exactDetectionIndex X P = 0) :
    ∃ F : AbelianSheaf X, stalkSupport F = P ∧ Nontrivial (F.H 0) := by
  classical
  by_contra hNone
  have hLower : (1 : ℕ∞) ≤ exactDetectionIndex X P := by
    apply le_sInf
    rintro i ⟨n, rfl, F, hF, hN⟩
    cases n with
    | zero => exact (hNone ⟨F, hF, hN⟩).elim
    | succ n => exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  rw [h] at hLower
  exact (by decide : ¬ ((1 : ℕ∞) ≤ 0)) hLower

private theorem isZero_of_empty_support {S : TopCat.{0}} (F : AbelianSheaf S)
    (hF : stalkSupport F = ∅) : IsZero F := by
  apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero (show TopCat.Sheaf G S from F)).mpr
  intro x
  change IsZero (TopCat.Presheaf.stalk (C := G) F.obj x)
  have h : ¬ Nontrivial (TopCat.Presheaf.stalk (C := G) F.obj x) := by
    intro hx
    have hx' : x ∈ stalkSupport F := hx
    rw [hF] at hx'
    exact hx'
  exact AddCommGrpCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp h)

private theorem sections_subsingleton_of_isZero {S : TopCat.{0}} (F : AbelianSheaf S)
    (hF : IsZero F) (U : Opens S) : Subsingleton (F.obj.obj (op U)) := by
  let T := (sheafSections (Opens.grothendieckTopology S) G).obj (op U)
  letI : T.Additive := ⟨by intros; rfl⟩
  exact AddCommGrpCat.subsingleton_of_isZero (T.map_isZero hF)

private theorem group_subsingleton_of_isZero {S : TopCat.{0}} (F : AbelianSheaf S)
    (hF : IsZero F) (U V : Opens S) (n : ℕ) : Subsingleton (group F U V n) := by
  rcases n with _ | (_ | n)
  · letI := sections_subsingleton_of_isZero F hF U
    letI := sections_subsingleton_of_isZero F hF V
    change Subsingleton (twoOpenDifferential F.obj U V).ker
    infer_instance
  · letI := sections_subsingleton_of_isZero F hF (U ⊓ V)
    change Subsingleton ((F.obj.obj (op (U ⊓ V))) ⧸ (twoOpenDifferential F.obj U V).range)
    exact (QuotientAddGroup.mk'_surjective _).subsingleton
  · change Subsingleton PUnit
    infer_instance

private theorem cechIndex_eq_top {U V : Opens X} {P : Set X}
    (h : ∀ F : AbelianSheaf X, stalkSupport F = P → ∀ n, Subsingleton (group F U V n)) :
    fixedCechDetectionIndex U V P = ⊤ := by
  unfold fixedCechDetectionIndex
  have hEq : {i : ℕ∞ | ∃ n : ℕ, (n : ℕ∞) = i ∧
      ∃ F : AbelianSheaf X, stalkSupport F = P ∧ Nontrivial (group F U V n)} = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun _ hi => ?_
    obtain ⟨n, -, F, hF, hN⟩ := hi
    exact (not_nontrivial_iff_subsingleton.mpr (h F hF n)) hN
  rw [hEq, sInf_empty]

/-- For any genuine two-open cover of Spec ℤ, the fixed-cover exact-support
infimum equals the infimum from actual derived sheaf cohomology. -/
theorem fixedCechDetectionIndex_eq_exact (U V : Opens X) (hCover : U ⊔ V = ⊤) (P : Set X) :
    fixedCechDetectionIndex U V P = exactDetectionIndex X P := by
  classical
  have hClass := SpecIntExactDetection.specInt_exactDetectionIndex_classification P
  by_cases hP : P.Nonempty ∧ ((⊥ : PrimeSpectrum ℤ) ∉ P ∨ (Pᶜ).Finite)
  · rw [if_pos hP] at hClass
    rw [hClass]
    obtain ⟨F, hF, hN⟩ := exists_H0_witness hClass
    letI := hN
    have hC : Nontrivial (group F U V 0) := (twoOpenH0Equiv F U V hCover).injective.nontrivial
    exact le_antisymm (sInf_le ⟨0, rfl, F, hF, hC⟩) bot_le
  · rw [if_neg hP] at hClass
    rw [hClass]
    apply cechIndex_eq_top
    intro F hF n
    by_cases hNonempty : P.Nonempty
    · have hη : (⊥ : PrimeSpectrum ℤ) ∈ P := by
        by_contra hn
        exact hP ⟨hNonempty, Or.inl hn⟩
      have hFin : ¬ (Pᶜ).Finite := fun h => hP ⟨hNonempty, Or.inr h⟩
      exact (SpecIntExactDetection.no_support_of_generic_and_infinite_compl hη hFin ⟨F, hF⟩).elim
    · have hEmpty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hNonempty
      exact group_subsingleton_of_isZero F (isZero_of_empty_support F (hF.trans hEmpty)) U V n

end

end ManuscriptAudit.SpecIntCechDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.SpecIntCechDetection.twoOpenH0Equiv,
      ``ManuscriptAudit.SpecIntCechDetection.fixedCechDetectionIndex_eq_exact] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
