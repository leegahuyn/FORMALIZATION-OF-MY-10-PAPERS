import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientAcyclic

/-!
# The native point-coefficient sheaf on arbitrary open covers

For each point select one member of the cover containing it. The Čech
cocycle then gives an explicit primitive. Both this cover calculation
and native derived degree one vanish for the same coefficient sheaf.
-/

namespace ManuscriptAudit.PointCoefficientCoverCohomology

open CategoryTheory CategoryTheory.Abelian TopologicalSpace
open PointCoefficientSheaf PointCoefficientExact ClosedSupportDetection

noncomputable section

variable {X : TopCat.{0}} (P : Set X) {ι : Type*} (U : ι → Opens X)
variable (A : P → Type) [∀ p : P, AddCommGroup (A p)]

abbrev OneCochain := ∀ i j, Sections P A (U i ⊓ U j)

def IsOneCocycle (c : OneCochain P U A) : Prop :=
  ∀ (i j k : ι) (p : P) (hi : p.val ∈ U i) (hj : p.val ∈ U j) (hk : p.val ∈ U k),
    c i j ⟨p, ⟨hi,hj⟩⟩ + c j k ⟨p, ⟨hj,hk⟩⟩ = c i k ⟨p, ⟨hi,hk⟩⟩

def IsCoboundary (c : OneCochain P U A) : Prop :=
  ∃ a : ∀ i, Sections P A (U i),
    ∀ i j (q : PointsIn P (U i ⊓ U j)),
      c i j q = a j ⟨q.val,q.property.2⟩ - a i ⟨q.val,q.property.1⟩

theorem cocycle_is_coboundary (hCover : iSup U = ⊤)
    (c : OneCochain P U A) (hc : IsOneCocycle P U A c) :
    IsCoboundary P U A c := by
  classical
  have h (p : P) : ∃ i, p.val ∈ U i := by
    apply Opens.mem_iSup.mp
    rw [hCover]
    trivial
  let j := fun p : P => Classical.choose (h p)
  have hj (p : P) : p.val ∈ U (j p) := Classical.choose_spec (h p)
  let a (i : ι) (q : PointsIn P (U i)) : A q.val :=
    c (j q.val) i ⟨q.val, ⟨hj q.val,q.property⟩⟩
  refine ⟨a, ?_⟩
  intro i k q
  apply eq_sub_iff_add_eq.mpr
  simpa only [a, add_comm] using hc (j q.val) i k q.val (hj q.val) q.property.1 q.property.2

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

theorem actual_cover_and_derived_degree_one (M : P → AddCommGrpCat.{0})
    (hCover : iSup U = ⊤) :
    (∀ c : OneCochain P U (fun p => (M p : Type)),
      IsOneCocycle P U (fun p => (M p : Type)) c →
        IsCoboundary P U (fun p => (M p : Type)) c) ∧
      Subsingleton ((coefficientSheaf P M).H 1) := by
  refine ⟨cocycle_is_coboundary P U _ hCover, ?_⟩
  exact PointCoefficientAcyclic.H_succ_subsingleton P M 0

end
end ManuscriptAudit.PointCoefficientCoverCohomology

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [
      ``ManuscriptAudit.PointCoefficientCoverCohomology.cocycle_is_coboundary,
      ``ManuscriptAudit.PointCoefficientCoverCohomology.actual_cover_and_derived_degree_one] do
    let ax ← collectAxioms name
    let bad := ax.filter fun x => !allowed.contains x
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
