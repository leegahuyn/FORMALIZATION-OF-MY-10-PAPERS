import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Topology
import PrimalitySheafVerification.ManuscriptAudit.ExactSupportDetection

/-!
# Exact support on arbitrary sets of closed points

The coproduct of the point skyscraper sheaves has exactly the prescribed
stalk support, even if the indexing set is not closed. This gives
degree-zero exact-support detection for every nonempty set of nonzero
primes of Spec ℤ in Paper 6, physical p. 200.
-/

namespace ManuscriptAudit.ClosedPointSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection ManuscriptAudit.ExactSupportDetection
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 12000

private abbrev G := AddCommGrpCat.{0}

private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

private def factor {X : TopCat.{0}} (P : Set X) (p : P) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf (p : X) (AddCommGrpCat.of (ZMod 2))

/-- Coproduct of the point skyscraper sheaves indexed by the prescribed set. -/
def supportSheaf (X : TopCat.{0}) (P : Set X) : AbelianSheaf X :=
  ∐ factor P

private abbrev stalkAt {X : TopCat.{0}} (x : X) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x

private theorem stalkAt_factor_isZero {X : TopCat.{0}} (P : Set X) (p : P) {x : X}
    (h : ¬ Specializes (p : X) x) : IsZero ((stalkAt x).obj (factor P p)) := by
  classical
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal
    (p : X) (AddCommGrpCat.of (ZMod 2)) h).isZero

private theorem mapCoproduct_isZero {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] {ι : Type*} (F : C ⥤ D) (objects : ι → C)
    [HasCoproduct objects] [PreservesColimit (Discrete.functor objects) F]
    (h : ∀ i, IsZero (F.obj (objects i))) : IsZero (F.obj (∐ objects)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  exact Cofan.IsColimit.hom_ext
    (isColimitOfHasCoproductOfPreservesColimit F objects) _ _
    (fun i => (h i).eq_of_src _ _)

private theorem outside_stalk_isZero {X : TopCat.{0}} {P : Set X}
    (hClosed : ∀ x ∈ P, IsClosed ({x} : Set X)) {x : X} (hx : x ∉ P) :
    IsZero ((stalkAt x).obj (supportSheaf X P)) := by
  classical
  letI : PreservesColimitsOfSize.{0, 0} (stalkAt x) :=
    (stalkSkyscraperSheafAdjunction (C := G) x).leftAdjoint_preservesColimits
  change IsZero ((stalkAt x).obj (∐ factor P))
  apply mapCoproduct_isZero (stalkAt x) (factor P)
  intro p
  have h : ¬ Specializes (p : X) x := by
    intro hsp
    have hm : x ∈ ({(p : X)} : Set X) :=
      hsp.mem_closed (hClosed (p : X) p.property) (by simp)
    exact hx ((Set.mem_singleton_iff.mp hm).symm ▸ p.property)
  exact (stalkAt_factor_isZero P p h).eq_of_src _ _

private theorem nontrivial_of_factor {X : TopCat.{0}} (P : Set X) (p : P)
    (T : AbelianSheaf X ⥤ G) (hp : Nontrivial (T.obj (factor P p))) :
    Nontrivial (T.obj (supportSheaf X P)) := by
  classical
  letI := hp
  let j : factor P p ⟶ supportSheaf X P := Sigma.ι (factor P) p
  let components : (q : P) → (factor P q ⟶ factor P p) :=
    fun q => if h : q = p then eqToHom (congrArg (factor P) h) else 0
  let r : supportSheaf X P ⟶ factor P p := Sigma.desc components
  have hr : j ≫ r = 𝟙 _ := by
    change Sigma.ι (factor P) p ≫ Sigma.desc components = _
    rw [Sigma.ι_desc]
    simp [components]
  have h : T.map j ≫ T.map r = 𝟙 _ := by rw [← T.map_comp, hr, T.map_id]
  have hl : Function.LeftInverse (T.map r) (T.map j) := by
    intro a
    change (T.map j ≫ T.map r) a = a
    rw [h, AddCommGrpCat.id_apply]
  exact hl.injective.nontrivial

/-- The stalk support is exactly the designated set of closed points. -/
theorem supportSheaf_support_eq {X : TopCat.{0}} {P : Set X}
    (hClosed : ∀ x ∈ P, IsClosed ({x} : Set X)) :
    stalkSupport (supportSheaf X P) = P := by
  classical
  ext x
  constructor
  · intro h
    by_contra hx
    letI := AddCommGrpCat.subsingleton_of_isZero (outside_stalk_isZero hClosed hx)
    change Nontrivial ((stalkAt x).obj (supportSheaf X P)) at h
    obtain ⟨a, b, hab⟩ := h
    exact hab (Subsingleton.elim a b)
  · intro hx
    let p : P := ⟨x, hx⟩
    have hp : Nontrivial ((stalkAt x).obj (factor P p)) := by
      let e := skyscraperPresheafStalkOfSpecializes x (AddCommGrpCat.of (ZMod 2))
        (specializes_rfl : Specializes x x)
      exact e.symm.addCommGroupIsoToAddEquiv.injective.nontrivial
    exact nontrivial_of_factor P p (stalkAt x) hp

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private def topIsTerminal (X : TopCat.{0}) : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- A component at any point of the indexing set supplies nonzero native H⁰. -/
theorem supportSheaf_H0_nontrivial {X : TopCat.{0}} {P : Set X} (hP : P.Nonempty) :
    Nontrivial ((supportSheaf X P).H 0) := by
  classical
  obtain ⟨x, hx⟩ := hP
  let p : P := ⟨x, hx⟩
  let T := (sheafSections (Opens.grothendieckTopology X) G).obj (op (⊤ : Opens X))
  have hp : Nontrivial (T.obj (factor P p)) := by
    have hObj : T.obj (factor P p) = AddCommGrpCat.of (ZMod 2) := by
      change (if (p : X) ∈ (⊤ : Opens X) then AddCommGrpCat.of (ZMod 2) else terminal G) = _
      rw [if_pos (show (p : X) ∈ (⊤ : Opens X) by simp)]
    rw [hObj]
    infer_instance
  letI : Nontrivial ((supportSheaf X P).obj.obj (op (⊤ : Opens X))) :=
    nontrivial_of_factor P p T hp
  exact (Sheaf.H.equiv₀ (supportSheaf X P) (topIsTerminal X)).symm.injective.nontrivial

/-- Every nonempty set of closed points has exact-support detection degree zero. -/
theorem exactDetectionIndex_eq_zero_of_nonempty_closed_points {X : TopCat.{0}} {P : Set X}
    (hClosed : ∀ x ∈ P, IsClosed ({x} : Set X)) (hNonempty : P.Nonempty) :
    exactDetectionIndex X P = 0 := by
  apply le_antisymm _ bot_le
  exact sInf_le ⟨0, rfl, supportSheaf X P, supportSheaf_support_eq hClosed,
    supportSheaf_H0_nontrivial hNonempty⟩

/-- Paper 6. Arbitrary nonempty sets of nonzero primes in Spec ℤ have exact-support index zero. -/
theorem specInt_exactDetectionIndex_eq_zero {P : Set (PrimeSpectrum ℤ)}
    (hNonzero : ∀ x ∈ P, x.asIdeal ≠ ⊥) (hNonempty : P.Nonempty) :
    exactDetectionIndex (TopCat.of (PrimeSpectrum ℤ)) P = 0 := by
  apply exactDetectionIndex_eq_zero_of_nonempty_closed_points _ hNonempty
  intro x hx
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).2
    (IsPrime.to_maximal_ideal (hNonzero x hx))

end

end ManuscriptAudit.ClosedPointSupportDetection

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.ClosedPointSupportDetection.supportSheaf_support_eq,
      ``ManuscriptAudit.ClosedPointSupportDetection.supportSheaf_H0_nontrivial,
      ``ManuscriptAudit.ClosedPointSupportDetection.exactDetectionIndex_eq_zero_of_nonempty_closed_points,
      ``ManuscriptAudit.ClosedPointSupportDetection.specInt_exactDetectionIndex_eq_zero] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
