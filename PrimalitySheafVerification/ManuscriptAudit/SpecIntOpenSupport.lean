import Lean.Util.CollectAxioms
import Mathlib.Topology.Sets.Opens
import PrimalitySheafVerification.ManuscriptAudit.SpecIntExactDetection

/-!
# Exact-support detection after restriction to an open of Spec ℤ

The support index computed from the manuscript's native Zariski sheaf
cohomology is unchanged on an open containing the support. This applies
to every principal open and uses only the topology of the prime spectrum.
-/

namespace ManuscriptAudit.SpecIntOpenSupport

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open ClosedSupportDetection ExactSupportDetection GenericPointSupportDetection
open SpecIntExactDetection

noncomputable section

private abbrev Y := PrimeSpectrum ℤ
private abbrev space (U : Opens Y) := TopCat.of U

local instance (S : TopCat.{0}) : HasExt.{0} (AbelianSheaf S) :=
  IsGrothendieckAbelian.hasExt _

private theorem generic_specializes (x : Y) : Specializes (⊥ : Y) x :=
  (PrimeSpectrum.le_iff_specializes _ _).mp bot_le

private theorem subtype_generic_specializes (U : Opens Y) (hU : (⊥ : Y) ∈ U)
    (x : U) : Specializes (⟨⊥, hU⟩ : U) x := by
  exact U.isOpenEmbedding'.isEmbedding.isInducing.specializes_iff.mp
    (generic_specializes x.val)

private theorem closed_subtype_point (U : Opens Y) (x : U) (hx : x.val ≠ ⊥) :
    IsClosed ({x} : Set U) := by
  have hPrime : x.val.asIdeal ≠ ⊥ := by
    intro h
    exact hx (PrimeSpectrum.ext_iff.mpr (h.trans PrimeSpectrum.asIdeal_bot.symm))
  have hBase : IsClosed ({x.val} : Set Y) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal x.val).2 (IsPrime.to_maximal_ideal hPrime)
  have hPreimage : (Subtype.val : U → Y) ⁻¹' {x.val} = {x} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Subtype.ext_iff]
  rw [← hPreimage]
  exact hBase.preimage continuous_subtype_val

private theorem subtype_compl_finite_of_contains_open (U : Opens Y) (hU : (⊥ : Y) ∈ U)
    {P : Set U} (V : Opens U) (hV : (⟨⊥, hU⟩ : U) ∈ V) (hVP : (V : Set U) ⊆ P) :
    Pᶜ.Finite := by
  let W : Opens Y := ⟨Subtype.val '' (V : Set U), U.isOpenEmbedding'.isOpenMap _ V.isOpen⟩
  have hW : (⊥ : Y) ∈ W := ⟨⟨⊥, hU⟩, hV, rfl⟩
  have hFin := (specInt_generic_neighborhood_compl_finite W hW).preimage
    (Subtype.val_injective.injOn (s := (Subtype.val : U → Y) ⁻¹' ((W : Set Y)ᶜ)))
  refine hFin.subset ?_
  intro x hx hWx
  obtain ⟨y, hy, hyx⟩ := hWx
  exact hx (hVP ((Subtype.ext hyx : y = x) ▸ hy))

private theorem cofinite_iff_image_cofinite (U : Opens Y) (hU : (⊥ : Y) ∈ U) (P : Set U) :
    ((Subtype.val '' P : Set Y)ᶜ).Finite ↔ Pᶜ.Finite := by
  constructor
  · intro h
    refine (h.preimage (Subtype.val_injective.injOn (s := (Subtype.val : U → Y) ⁻¹'
      (Subtype.val '' P : Set Y)ᶜ))).subset ?_
    intro x hx hx'
    obtain ⟨y, hy, he⟩ := hx'
    exact hx ((Subtype.ext he : y = x) ▸ hy)
  · intro h
    have hUFin := specInt_generic_neighborhood_compl_finite U hU
    refine (hUFin.union (h.image Subtype.val)).subset ?_
    intro x hx
    by_cases hxU : x ∈ U
    · exact Or.inr ⟨⟨x, hxU⟩, fun hP => hx ⟨⟨x, hxU⟩, hP, rfl⟩, rfl⟩
    · exact Or.inl hxU

private theorem open_of_cofinite_generic (U : Opens Y) (hU : (⊥ : Y) ∈ U)
    {P : Set U} (hη : (⟨⊥, hU⟩ : U) ∈ P) (hFin : Pᶜ.Finite) : IsOpen P := by
  have hClosed : IsClosed Pᶜ := by
    have hUnion : (⋃ x ∈ Pᶜ, ({x} : Set U)) = Pᶜ := by ext x; simp
    rw [← hUnion]
    exact hFin.isClosed_biUnion fun x hx => closed_subtype_point U x (fun h =>
      hx ((Subtype.ext h.symm : (⟨⊥, hU⟩ : U) = x) ▸ hη))
  simpa only [compl_compl] using hClosed.isOpen_compl

private theorem exists_closed_point_in_generic_open (U : Opens Y) (hU : (⊥ : Y) ∈ U)
    {P : Set U} (hOpen : IsOpen P) (hη : (⟨⊥, hU⟩ : U) ∈ P) :
    ∃ x ∈ P, IsClosed ({x} : Set U) := by
  let V : Opens Y := ⟨Subtype.val '' P, U.isOpenEmbedding'.isOpenMap P hOpen⟩
  have hV : (⊥ : Y) ∈ V := ⟨⟨⊥, hU⟩, hη, rfl⟩
  obtain ⟨x, hx, hNonzero⟩ := specInt_neighborhood_contains_nonzero_prime V hV
  obtain ⟨y, hy, hyx⟩ := hx
  exact ⟨y, hy, closed_subtype_point U y (fun h => hNonzero (hyx.symm.trans h))⟩

private theorem detection_eq_top_of_no_support (X : TopCat.{0}) (P : Set X)
    (h : ¬ ∃ F : AbelianSheaf X, stalkSupport F = P) : exactDetectionIndex X P = ⊤ := by
  unfold exactDetectionIndex
  apply eq_trans (congrArg sInf ?_) sInf_empty
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro i ⟨n, hn, F, hF, hH⟩
  exact h ⟨F, hF⟩

private theorem openDetectionIndex_classification (U : Opens Y) (hU : (⊥ : Y) ∈ U) (P : Set U) :
    exactDetectionIndex (space U) P =
      @ite ℕ∞ (P.Nonempty ∧ ((⟨⊥, hU⟩ : U) ∉ P ∨ Pᶜ.Finite))
        (Classical.propDecidable _) 0 ⊤ := by
  classical
  by_cases hNonempty : P.Nonempty
  · by_cases hη : (⟨⊥, hU⟩ : U) ∈ P
    · by_cases hFin : Pᶜ.Finite
      · rw [if_pos ⟨hNonempty, Or.inr hFin⟩]
        have hOpen := open_of_cofinite_generic U hU hη hFin
        obtain ⟨x, hx, hClosed⟩ := exists_closed_point_in_generic_open U hU hOpen hη
        exact CofiniteSupportDetection.exactDetectionIndex_eq_zero_of_open_with_generic_and_closed_point
          (X := space U) hOpen (subtype_generic_specializes U hU) hx hClosed
      · rw [if_neg (by simp [hη, hFin])]
        apply detection_eq_top_of_no_support
        rintro ⟨F, hF⟩
        have hη' : (⟨⊥, hU⟩ : U) ∈ stalkSupport F := hF.symm ▸ hη
        obtain ⟨V, hV, hVP⟩ := exists_open_subset_support F
          (subtype_generic_specializes U hU) hη'
        exact hFin (subtype_compl_finite_of_contains_open U hU V hV (hF ▸ hVP))
    · rw [if_pos ⟨hNonempty, Or.inl hη⟩]
      apply ClosedPointSupportDetection.exactDetectionIndex_eq_zero_of_nonempty_closed_points _ hNonempty
      intro x hx
      exact closed_subtype_point U x (fun h => hη ((Subtype.ext h : x = ⟨⊥, hU⟩) ▸ hx))
  · have hEmpty : P = ∅ := Set.not_nonempty_iff_eq_empty.mp hNonempty
    rw [if_neg (fun h => hNonempty h.1), hEmpty]
    exact exactDetectionIndex_empty (space U)

/-- The manuscript's restriction invariance for the actual underlying Zariski sheaf index. -/
theorem exactDetectionIndex_restriction (U : Opens Y) (P : Set U) :
    exactDetectionIndex (TopCat.of Y) (Subtype.val '' P) = exactDetectionIndex (space U) P := by
  classical
  by_cases hP : P.Nonempty
  · obtain ⟨x, hx⟩ := hP
    have hU : (⊥ : Y) ∈ U := (generic_specializes x.val).mem_open U.isOpen x.property
    have hGeneric :
        (⊥ : Y) ∈ (Subtype.val '' P : Set Y) ↔ (⟨⊥, hU⟩ : U) ∈ P :=
      ⟨fun ⟨y, hy, hyη⟩ => (Subtype.ext hyη : y = ⟨⊥, hU⟩) ▸ hy,
        fun h => ⟨⟨⊥, hU⟩, h, rfl⟩⟩
    rw [specInt_exactDetectionIndex_classification, openDetectionIndex_classification U hU,
      hGeneric, cofinite_iff_image_cofinite U hU, Set.image_nonempty]
  · have hEmpty := Set.not_nonempty_iff_eq_empty.mp hP
    rw [hEmpty, Set.image_empty, exactDetectionIndex_empty, exactDetectionIndex_empty]

end

end ManuscriptAudit.SpecIntOpenSupport

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.SpecIntOpenSupport.exactDetectionIndex_restriction
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
