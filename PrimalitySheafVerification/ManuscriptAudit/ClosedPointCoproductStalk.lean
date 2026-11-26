import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ClosedPointCoproduct

namespace ManuscriptAudit.ClosedPointSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 4000
set_option maxHeartbeats 12000
set_option maxRecDepth 512

private abbrev G := AddCommGrpCat.{0}
private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

local instance stalkPointFactor_hasCoproduct {X : TopCat.{0}} (P : Set X) :
    HasCoproduct (pointFactor P) :=
  abelianSheaf_hasDiscreteColimit X (Discrete.functor (pointFactor P))

private abbrev stalkAt {X : TopCat.{0}} (x : X) : AbelianSheaf X ⥤ G :=
  TopCat.Sheaf.forget G X ⋙ TopCat.Presheaf.stalkFunctor G x

private theorem stalkAt_factor_isZero {X : TopCat.{0}} (P : Set X) (p : P) {x : X}
    (h : ¬ Specializes (p : X) x) : IsZero ((stalkAt x).obj (pointFactor P p)) := by
  classical
  exact (skyscraperPresheafStalkOfNotSpecializesIsTerminal
    (p : X) (AddCommGrpCat.of (ZMod 2)) h).isZero

private theorem outside_stalk_isZero {X : TopCat.{0}} {P : Set X}
    (hClosed : ∀ x ∈ P, IsClosed ({x} : Set X)) {x : X} (hx : x ∉ P) :
    IsZero ((stalkAt x).obj (supportSheaf X P)) := by
  classical
  letI : PreservesColimitsOfSize.{0, 0} (stalkAt x) :=
    (stalkSkyscraperSheafAdjunction (C := G) x).leftAdjoint_preservesColimits
  change IsZero ((stalkAt x).obj (∐ pointFactor P))
  apply mapCoproduct_isZero (stalkAt x) (pointFactor P)
  intro p
  have h : ¬ Specializes (p : X) x := by
    intro hsp
    have hm : x ∈ ({(p : X)} : Set X) :=
      hsp.mem_closed (hClosed (p : X) p.property) (by simp)
    have he : x = (p : X) := Set.mem_singleton_iff.mp hm
    exact hx (by simpa [he] using p.property)
  exact stalkAt_factor_isZero P p h

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
    have hp : Nontrivial ((stalkAt x).obj (pointFactor P p)) := by
      let e := skyscraperPresheafStalkOfSpecializes x (AddCommGrpCat.of (ZMod 2))
        (specializes_rfl : Specializes x x)
      exact e.symm.addCommGroupIsoToAddEquiv.injective.nontrivial
    exact supportSheaf_nontrivial_of_factor P p (stalkAt x) hp

end

end ManuscriptAudit.ClosedPointSupportDetection

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ClosedPointSupportDetection.supportSheaf_support_eq
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName =>
    !([``propext, ``Classical.choice, ``Quot.sound] : List Name).contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
