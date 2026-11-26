import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.RingTheory.PrincipalIdealDomain
import PrimalitySheafVerification.ManuscriptAudit.ExactSupportDetection
import PrimalitySheafVerification.ManuscriptAudit.GenericPointSupportDetection

/-!
# Exact support of cofinite subsets containing the generic point

Take the kernel of the generic skyscraper's maps to the omitted closed
points. A closed point in the desired support supplies degree-zero
cohomology after taking a binary product with its skyscraper.
-/

namespace ManuscriptAudit.CofiniteSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ExactSupportDetection
open scoped ZeroObject

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1200000

private abbrev G := AddCommGrpCat.{0}
private abbrev A := AddCommGrpCat.of (ZMod 2)
private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private def sk {X : TopCat.{0}} (x : X) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf x A

private abbrev stalkAt {X : TopCat.{0}} (x : X) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x

local instance stalkAt_additive {X : TopCat.{0}} (x : X) : (stalkAt x).Additive :=
  inferInstanceAs ((TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x).Additive)

local instance stalkAt_preservesZeroMorphisms {X : TopCat.{0}} (x : X) :
    (stalkAt x).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_additive (stalkAt x)

local instance stalkAt_preservesFiniteLimits {X : TopCat.{0}} (x : X) :
    PreservesFiniteLimits (stalkAt x) :=
  inferInstanceAs (PreservesFiniteLimits (TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x))

private def toPoint {X : TopCat.{0}} (η x : X) (h : Specializes η x) : sk η ⟶ sk x := by
  classical
  let e := skyscraperPresheafStalkOfSpecializes η A h
  exact (stalkSkyscraperSheafAdjunction (C := G) x).homEquiv (sk η) A e.hom

private theorem map_toPoint_mono {X : TopCat.{0}} (η x : X) (h : Specializes η x) :
    Mono ((stalkAt x).map (toPoint η x h)) := by
  classical
  let adj := stalkSkyscraperSheafAdjunction (C := G) x
  let e := skyscraperPresheafStalkOfSpecializes η A h
  have he : (stalkAt x).map (toPoint η x h) ≫ adj.counit.app A = e.hom := by
    change (stalkAt x).map (adj.homEquiv (sk η) A e.hom) ≫ adj.counit.app A = e.hom
    simpa only [adj.homEquiv_counit] using
      (adj.homEquiv (sk η) A).symm_apply_apply e.hom
  exact mono_of_mono_fac he

private abbrev omittedProduct {X : TopCat.{0}} (Q : Set X) : AbelianSheaf X :=
  ∏ᶜ fun y : Q => sk (y : X)

private theorem omittedProduct_support_eq {X : TopCat.{0}} {Q : Set X} (hQ : IsClosed Q) :
    stalkSupport (omittedProduct Q) = Q :=
  ExactSupportDetection.supportSheaf_support_eq hQ

private def testOmitted {X : TopCat.{0}} (η : X) (hη : ∀ x : X, Specializes η x)
    (Q : Set X) : sk η ⟶ omittedProduct Q :=
  Pi.lift (fun q : Q => toPoint η q (hη q))

private theorem map_testOmitted_mono {X : TopCat.{0}} (η : X) (hη : ∀ x : X, Specializes η x)
    (Q : Set X) (q : Q) : Mono ((stalkAt (q : X)).map (testOmitted η hη Q)) := by
  let F := stalkAt (q : X)
  letI := map_toPoint_mono η (q : X) (hη q)
  have hf : F.map (testOmitted η hη Q) ≫ F.map (Pi.π (fun y : Q => sk (y : X)) q) =
      F.map (toPoint η q (hη q)) := by
    rw [← F.map_comp, testOmitted, Pi.lift_π]
  exact mono_of_mono_fac hf

private theorem kernel_stalk_isZero {X : TopCat.{0}} (η : X) (hη : ∀ x : X, Specializes η x)
    {P : Set X} {x : X} (hx : x ∉ P) :
    IsZero ((stalkAt x).obj (kernel (testOmitted η hη Pᶜ))) := by
  let q : ↑(Pᶜ : Set X) := ⟨x, hx⟩
  letI := map_testOmitted_mono η hη Pᶜ q
  exact (isZero_kernel_of_mono _).of_iso (PreservesKernel.iso (stalkAt x)
    (testOmitted η hη Pᶜ))

private theorem kernel_stalk_nontrivial {X : TopCat.{0}} (η : X)
    (hη : ∀ x : X, Specializes η x) {P : Set X} (hP : IsClosed Pᶜ) {x : X} (hx : x ∈ P) :
    Nontrivial ((stalkAt x).obj (kernel (testOmitted η hη Pᶜ))) := by
  classical
  let F := stalkAt x
  letI : F.PreservesZeroMorphisms := stalkAt_preservesZeroMorphisms x
  letI : PreservesFiniteLimits F := stalkAt_preservesFiniteLimits x
  let f := testOmitted η hη Pᶜ
  have hNot : ¬ Nontrivial (F.obj (omittedProduct Pᶜ)) := by
    intro h
    have hx' : x ∈ stalkSupport (omittedProduct Pᶜ) := h
    rw [omittedProduct_support_eq hP] at hx'
    exact hx' hx
  have hZero : IsZero (F.obj (omittedProduct Pᶜ)) :=
    AddCommGrpCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp hNot)
  have hf : F.map f = 0 := hZero.eq_of_tgt _ _
  let e : F.obj (kernel f) ≅ F.obj (sk η) :=
    PreservesKernel.iso F f ≪≫ eqToIso (congrArg (fun g => kernel g) hf) ≪≫
      kernelZeroIsoSource
  letI : Nontrivial (F.obj (sk η)) :=
    (skyscraperPresheafStalkOfSpecializes η A (hη x)).symm.addCommGroupIsoToAddEquiv.injective.nontrivial
  exact e.symm.addCommGroupIsoToAddEquiv.injective.nontrivial

private theorem nontrivial_of_retract {X : TopCat.{0}} {U V : AbelianSheaf X}
    (F : AbelianSheaf X ⥤ G) (i : U ⟶ V) (r : V ⟶ U) (h : i ≫ r = 𝟙 _)
    (hU : Nontrivial (F.obj U)) : Nontrivial (F.obj V) := by
  letI := hU
  have hComp : F.map i ≫ F.map r = 𝟙 _ := by rw [← F.map_comp, h, F.map_id]
  have hi : Function.LeftInverse (F.map r) (F.map i) := by
    intro u
    change (F.map i ≫ F.map r) u = u
    rw [hComp, AddCommGrpCat.id_apply]
  exact hi.injective.nontrivial

private theorem point_H0_nontrivial {X : TopCat.{0}} (x : X) : Nontrivial ((sk x).H 0) := by
  classical
  have hSections : (sk x).obj.obj (op (⊤ : Opens X)) = A := by
    change (if x ∈ (⊤ : Opens X) then A else terminal G) = A
    rw [if_pos (show x ∈ (⊤ : Opens X) by simp)]
  letI : Nontrivial ((sk x).obj.obj (op (⊤ : Opens X))) := by
    rw [hSections]
    infer_instance
  let hT : IsTerminal (⊤ : Opens X) :=
    IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)
  exact (Sheaf.H.equiv₀ (sk x) hT).symm.injective.nontrivial

/-- An open set containing a generic point and an included closed point
has a native exact-support witness in degree zero. -/
theorem exactDetectionIndex_eq_zero_of_open_with_generic_and_closed_point
    {X : TopCat.{0}} {P : Set X} (hP : IsOpen P)
    {η x₀ : X} (hη : ∀ x : X, Specializes η x) (hx₀ : x₀ ∈ P)
    (hx₀Closed : IsClosed ({x₀} : Set X)) : exactDetectionIndex X P = 0 := by
  classical
  let U := kernel (testOmitted η hη Pᶜ)
  let V := U ⨯ sk x₀
  have hSupport : stalkSupport V = P := by
    ext x
    constructor
    · intro hx
      by_contra hxP
      let F := stalkAt x
      letI : PreservesFiniteLimits F := stalkAt_preservesFiniteLimits x
      have hU : IsZero (F.obj U) := kernel_stalk_isZero η hη hxP
      have hsp : ¬ Specializes x₀ x := by
        intro hsp
        have hx' : x ∈ ({x₀} : Set X) := hsp.mem_closed hx₀Closed (by simp)
        exact hxP ((Set.mem_singleton_iff.mp hx').symm ▸ hx₀)
      have hSk : IsZero (F.obj (sk x₀)) :=
        (skyscraperPresheafStalkOfNotSpecializesIsTerminal x₀ A hsp).isZero
      have hZero : IsZero (F.obj V) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        exact BinaryFan.IsLimit.hom_ext
          (isLimitOfHasBinaryProductOfPreservesLimit F U (sk x₀))
          (hU.eq_of_tgt _ _) (hSk.eq_of_tgt _ _)
      letI := AddCommGrpCat.subsingleton_of_isZero hZero
      change Nontrivial (F.obj V) at hx
      obtain ⟨a, b, hab⟩ := hx
      exact hab (Subsingleton.elim a b)
    · intro hx
      exact nontrivial_of_retract (stalkAt x) (prod.lift (𝟙 U) (0 : U ⟶ sk x₀)) prod.fst
        (prod.lift_fst _ _) (kernel_stalk_nontrivial η hη hP.isClosed_compl hx)
  have hH0 : Nontrivial (V.H 0) :=
    nontrivial_of_retract (Sheaf.functorH (Opens.grothendieckTopology X) 0)
      (prod.lift (0 : sk x₀ ⟶ U) (𝟙 (sk x₀))) prod.snd
      (prod.lift_snd _ _) (point_H0_nontrivial x₀)
  exact le_antisymm (sInf_le ⟨0, rfl, V, hSupport, hH0⟩) bot_le

private theorem closed_nonzero_prime {x : PrimeSpectrum ℤ} (hx : x ≠ ⊥) :
    IsClosed ({x} : Set (PrimeSpectrum ℤ)) := by
  refine (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2
    (IsPrime.to_maximal_ideal ?_)
  intro h
  exact hx (PrimeSpectrum.ext_iff.mpr (h.trans PrimeSpectrum.asIdeal_bot.symm))

/-- A cofinite support that includes the generic point of Spec ℤ has exact detection degree zero. -/
theorem specInt_exactDetectionIndex_eq_zero_of_cofinite_generic
    {P : Set (PrimeSpectrum ℤ)} (hη : (⊥ : PrimeSpectrum ℤ) ∈ P) (hFin : Pᶜ.Finite) :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) P = 0 := by
  have hClosed : IsClosed Pᶜ := by
    have hUnion : (⋃ x ∈ Pᶜ, ({x} : Set (PrimeSpectrum ℤ))) = Pᶜ := by ext x; simp
    rw [← hUnion]
    exact hFin.isClosed_biUnion fun x hx =>
      closed_nonzero_prime (fun h => hx (h.symm ▸ hη))
  have hOpen : IsOpen P := by simpa only [compl_compl] using hClosed.isOpen_compl
  let U : Opens (PrimeSpectrum ℤ) := ⟨P, hOpen⟩
  obtain ⟨x, hx, hxne⟩ :=
    GenericPointSupportDetection.specInt_neighborhood_contains_nonzero_prime U hη
  exact exactDetectionIndex_eq_zero_of_open_with_generic_and_closed_point
    (X := TopCat.of (PrimeSpectrum ℤ)) hOpen (η := (⊥ : PrimeSpectrum ℤ))
    (fun y => (PrimeSpectrum.le_iff_specializes _ _).mp bot_le) hx
    (closed_nonzero_prime hxne)

end

end ManuscriptAudit.CofiniteSupportDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.CofiniteSupportDetection.exactDetectionIndex_eq_zero_of_open_with_generic_and_closed_point,
      ``ManuscriptAudit.CofiniteSupportDetection.specInt_exactDetectionIndex_eq_zero_of_cofinite_generic] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
