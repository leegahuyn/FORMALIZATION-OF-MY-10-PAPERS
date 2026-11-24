import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.Topology.Sheaves.AddCommGrpCat

/-!
Paper 4, physical p. 114, Definition 3.18 quantifies over abelian sheaves
with support contained in P. Proposition 3.20 on p. 115 gives its monotonicity. With this quantifier, every nonempty closed P
has degree-zero detection. We take the infimum in the extended naturals,
so the empty set has index infinity.
-/

namespace ManuscriptAudit.ClosedSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1200000

private abbrev G := AddCommGrpCat.{0}

abbrev AbelianSheaf (X : TopCat.{0}) := Sheaf (Opens.grothendieckTopology X) G

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

/-- The support detected by nonzero stalks. -/
def stalkSupport {X : TopCat.{0}} (F : AbelianSheaf X) : Set X :=
  {x | Nontrivial (TopCat.Presheaf.stalk (C := G) (X := X) F.obj x)}

private def topIsTerminal (X : TopCat.{0}) : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

private theorem terminalGroup_subsingleton : Subsingleton (terminal G) := by
  have hZero : IsZero (0 : G) := isZero_zero G
  exact AddCommGrpCat.subsingleton_of_isZero
    (hZero.of_iso (terminalIsoIsTerminal hZero.isTerminal))

/-- A closed subset containing a point already supports a sheaf with
nonzero global degree-zero cohomology. -/
theorem closed_nonempty_has_degree_zero_witness (X : TopCat.{0}) {P : Set X}
    (hP : IsClosed P) (hp : P.Nonempty) :
    ∃ F : AbelianSheaf X, stalkSupport F ⊆ P ∧ Nontrivial (F.H 0) := by
  classical
  obtain ⟨p, hp⟩ := hp
  let F : AbelianSheaf X := skyscraperSheaf p (AddCommGrpCat.of (ZMod 2))
  refine ⟨F, ?_, ?_⟩
  · intro x hx
    by_contra hxP
    have hsp : ¬ Specializes p x := fun h => hxP (h.mem_closed hP hp)
    let e := skyscraperPresheafStalkOfNotSpecializes p (AddCommGrpCat.of (ZMod 2)) hsp
    letI : Subsingleton (terminal G) := terminalGroup_subsingleton
    letI : Subsingleton (TopCat.Presheaf.stalk (C := G) (X := X) F.obj x) :=
      e.addCommGroupIsoToAddEquiv.injective.subsingleton
    change Nontrivial (TopCat.Presheaf.stalk (C := G) (X := X) F.obj x) at hx
    obtain ⟨a, b, hab⟩ := hx
    exact hab (Subsingleton.elim a b)
  · have hSections : F.obj.obj (op (⊤ : Opens X)) = AddCommGrpCat.of (ZMod 2) := by
      change (if p ∈ (⊤ : Opens X) then AddCommGrpCat.of (ZMod 2) else terminal G) = _
      rw [if_pos (show p ∈ (⊤ : Opens X) by simp)]
    letI : Nontrivial (F.obj.obj (op (⊤ : Opens X))) := by
      rw [hSections]
      change Nontrivial (ZMod 2)
      infer_instance
    exact (Sheaf.H.equiv₀ F (topIsTerminal X)).symm.injective.nontrivial

/-- Detection degrees from Definition 3.18, embedded into the extended naturals. -/
def detectionDegrees (X : TopCat.{0}) (P : Set X) : Set ℕ∞ :=
  {i | ∃ n : ℕ, (n : ℕ∞) = i ∧
    ∃ F : AbelianSheaf X, stalkSupport F ⊆ P ∧ Nontrivial (F.H n)}

def detectionIndex (X : TopCat.{0}) (P : Set X) : ℕ∞ :=
  sInf (detectionDegrees X P)

/-- Paper 4, p. 115, Proposition 3.20. Enlarging the allowed support
can only enlarge the set of detection degrees. -/
theorem detectionIndex_antitone (X : TopCat.{0}) : Antitone (detectionIndex X) := by
  intro P Q hPQ
  apply sInf_le_sInf
  rintro i ⟨n, hi, F, hF, hn⟩
  exact ⟨n, hi, F, hF.trans hPQ, hn⟩

theorem detectionIndex_eq_zero_of_nonempty_closed (X : TopCat.{0}) {P : Set X}
    (hP : IsClosed P) (hp : P.Nonempty) : detectionIndex X P = 0 := by
  have hDegree : (0 : ℕ∞) ∈ detectionDegrees X P :=
    ⟨0, rfl, closed_nonempty_has_degree_zero_witness X hP hp⟩
  exact le_antisymm (sInf_le hDegree) bot_le

theorem detectionIndex_empty (X : TopCat.{0}) : detectionIndex X ∅ = ⊤ := by
  have hEmpty : detectionDegrees X ∅ = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro i hi
    obtain ⟨n, _, F, hs, hn⟩ := hi
    have hF : IsZero F := by
      apply (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
        (show TopCat.Sheaf G X from F)).mpr
      intro x
      change IsZero (TopCat.Presheaf.stalk (C := G) (X := X) F.obj x)
      have hNot : ¬ Nontrivial (TopCat.Presheaf.stalk (C := G) (X := X) F.obj x) := fun h => hs h
      exact AddCommGrpCat.isZero_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp hNot)
    letI := Sheaf.subsingleton_H_of_isZero hF n
    obtain ⟨a, b, hab⟩ := hn
    exact hab (Subsingleton.elim a b)
  rw [detectionIndex, hEmpty, sInf_empty]

/-- If the restricted closed set is empty, shrinking changes the extended
detection index from zero to infinity. -/
theorem detectionIndex_changes_if_shrinking_removes_support (X : TopCat.{0})
    {P : Set X} (hP : IsClosed P) (hNonempty : P.Nonempty)
    (U : Opens X) (hDisjoint : Disjoint (U : Set X) P) :
    detectionIndex X P = 0 ∧
      detectionIndex (TopCat.of U) ((Subtype.val : U → X) ⁻¹' P) = ⊤ := by
  refine ⟨detectionIndex_eq_zero_of_nonempty_closed X hP hNonempty, ?_⟩
  have hEmpty : (Subtype.val : U → X) ⁻¹' P = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact Set.disjoint_left.mp hDisjoint x.property hx
  rw [hEmpty]
  exact detectionIndex_empty (TopCat.of U)

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``closed_nonempty_has_degree_zero_witness,
      ``detectionIndex_antitone, ``detectionIndex_eq_zero_of_nonempty_closed, ``detectionIndex_empty,
      ``detectionIndex_changes_if_shrinking_removes_support] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.ClosedSupportDetection
