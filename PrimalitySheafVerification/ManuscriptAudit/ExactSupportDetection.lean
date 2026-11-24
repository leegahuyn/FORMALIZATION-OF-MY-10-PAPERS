import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import PrimalitySheafVerification.ManuscriptAudit.ClosedSupportDetection

/-!
The lead paragraph of Paper 4, physical p. 114, uses equality of stalk
support with P. With arbitrary abelian sheaves, this version also has
degree-zero detection on every nonempty closed P.
-/

namespace ManuscriptAudit.ExactSupportDetection

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.ClosedSupportDetection
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1200000

private abbrev G := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩

private def factor {X : TopCat.{0}} (P : Set X) (p : P) : AbelianSheaf X := by
  classical
  exact skyscraperSheaf (p : X) (AddCommGrpCat.of (ZMod 2))

/-- Product of the finite skyscraper sheaves indexed by the requested set. -/
def supportSheaf (X : TopCat.{0}) (P : Set X) : AbelianSheaf X :=
  ∏ᶜ factor P

private def ev {X : TopCat.{0}} (U : Opens X) : AbelianSheaf X ⥤ G :=
  sheafToPresheaf (Opens.grothendieckTopology X) G ⋙ (evaluation _ G).obj (op U)

private instance {X : TopCat.{0}} (U : Opens X) : PreservesLimits (ev U) := by
  unfold ev
  infer_instance

private def projection {X : TopCat.{0}} (P : Set X) (p : P) :
    supportSheaf X P ⟶ factor P p :=
  Pi.π (factor P) p

private theorem factorSplit {X : TopCat.{0}} (P : Set X) (p : P) :
    ∃ j : factor P p ⟶ supportSheaf X P, j ≫ projection P p = 𝟙 _ := by
  classical
  let f : (q : P) → (factor P p ⟶ factor P q) :=
    fun q => if h : p = q then eqToHom (congrArg (factor P) h) else 0
  refine ⟨Pi.lift f, ?_⟩
  change Pi.lift f ≫ Pi.π (factor P) p = 𝟙 _
  rw [Pi.lift_π]
  simp [f]

private theorem nontrivial_of_factor {X : TopCat.{0}} (P : Set X) (p : P)
    (T : AbelianSheaf X ⥤ G) (hp : Nontrivial (T.obj (factor P p))) :
    Nontrivial (T.obj (supportSheaf X P)) := by
  letI := hp
  obtain ⟨j, hj⟩ := factorSplit P p
  have h : T.map j ≫ T.map (projection P p) = 𝟙 _ := by
    rw [← T.map_comp, hj, T.map_id]
  have hl : Function.LeftInverse (T.map (projection P p)) (T.map j) := by
    intro x
    change (T.map j ≫ T.map (projection P p)) x = x
    rw [h, AddCommGrpCat.id_apply]
  exact hl.injective.nontrivial

private def factor_sections_terminal {X : TopCat.{0}} (P : Set X) (p : P)
    (U : Opens X) (hp : (p : X) ∉ U) : IsTerminal ((ev U).obj (factor P p)) := by
  classical
  have heq : (ev U).obj (factor P p) = terminal G := by
    change (if (p : X) ∈ U then AddCommGrpCat.of (ZMod 2) else terminal G) = _
    rw [if_neg hp]
  exact heq.symm ▸ terminalIsTerminal

private theorem supportSheaf_sections_subsingleton {X : TopCat.{0}} (P : Set X)
    (U : Opens X) (h : Disjoint (U : Set X) P) :
    Subsingleton ((supportSheaf X P).obj.obj (op U)) := by
  have hZero : IsZero ((ev U).obj (supportSheaf X P)) := by
    apply IsZero.iff_id_eq_zero.mpr
    refine Fan.IsLimit.hom_ext
      (isLimitOfHasProductOfPreservesLimit (ev U) (factor P)) _ _ fun p => ?_
    have hp : (p : X) ∉ U :=
      fun hpU => Set.disjoint_left.mp h hpU p.property
    exact (factor_sections_terminal P p U hp).hom_ext _ _
  exact AddCommGrpCat.subsingleton_of_isZero hZero

private theorem supportSheaf_stalk_subsingleton_outside {X : TopCat.{0}}
    {P : Set X} (hP : IsClosed P) {x : X} (hx : x ∉ P) :
    Subsingleton (TopCat.Presheaf.stalk (C := G) (X := X) (supportSheaf X P).obj x) := by
  let V : Opens X := ⟨Pᶜ, hP.isOpen_compl⟩
  refine subsingleton_of_forall_eq 0 fun a => ?_
  obtain ⟨U, hUV, hxU, s, hs⟩ := TopCat.Presheaf.exists_le_germ_eq
    (C := G) (X := X) (supportSheaf X P).obj (x := x) a (V := V) (show x ∈ V from hx)
  have hDisjoint : Disjoint (U : Set X) P := by
    refine Set.disjoint_left.mpr fun y hyU hyP => ?_
    exact hUV hyU hyP
  letI := supportSheaf_sections_subsingleton P U hDisjoint
  rw [Subsingleton.elim s 0, map_zero] at hs
  exact hs.symm

/-- Stalk support of the product is exactly the designated closed set. -/
theorem supportSheaf_support_eq {X : TopCat.{0}} {P : Set X} (hP : IsClosed P) :
    stalkSupport (supportSheaf X P) = P := by
  classical
  ext x
  constructor
  · intro h
    by_contra hx
    letI := supportSheaf_stalk_subsingleton_outside hP hx
    change Nontrivial
      (TopCat.Presheaf.stalk (C := G) (X := X) (supportSheaf X P).obj x) at h
    obtain ⟨a, b, hab⟩ := h
    exact hab (Subsingleton.elim a b)
  · intro hx
    let t : AbelianSheaf X ⥤ G :=
      sheafToPresheaf (Opens.grothendieckTopology X) G ⋙ TopCat.Presheaf.stalkFunctor G x
    let p : P := ⟨x, hx⟩
    have h : Nontrivial (t.obj (factor P p)) := by
      let e := skyscraperPresheafStalkOfSpecializes x (AddCommGrpCat.of (ZMod 2))
        (specializes_rfl : Specializes x x)
      exact e.symm.addCommGroupIsoToAddEquiv.injective.nontrivial
    exact nontrivial_of_factor P p t h

private def topIsTerminal (X : TopCat.{0}) : IsTerminal (⊤ : Opens X) :=
  IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)

/-- A nonempty support supplies a nonzero degree-zero native cohomology class. -/
theorem supportSheaf_H0_nontrivial {X : TopCat.{0}} {P : Set X} (hP : P.Nonempty) :
    Nontrivial ((supportSheaf X P).H 0) := by
  classical
  obtain ⟨x, hx⟩ := hP
  let p : P := ⟨x, hx⟩
  have hp : Nontrivial ((ev (⊤ : Opens X)).obj (factor P p)) := by
    have heq : (ev (⊤ : Opens X)).obj (factor P p) = AddCommGrpCat.of (ZMod 2) := by
      change (if (p : X) ∈ (⊤ : Opens X) then AddCommGrpCat.of (ZMod 2) else terminal G) = _
      rw [if_pos (show (p : X) ∈ (⊤ : Opens X) by simp)]
    rw [heq]
    change Nontrivial (ZMod 2)
    infer_instance
  letI : Nontrivial ((supportSheaf X P).obj.obj (op (⊤ : Opens X))) :=
    nontrivial_of_factor P p (ev (⊤ : Opens X)) hp
  exact (Sheaf.H.equiv₀ (supportSheaf X P) (topIsTerminal X)).symm.injective.nontrivial

/-- The exact-support form of the p. 114 detection index. -/
def exactDetectionIndex (X : TopCat.{0}) (P : Set X) : ℕ∞ :=
  sInf {i | ∃ n : ℕ, (n : ℕ∞) = i ∧
    ∃ F : AbelianSheaf X, stalkSupport F = P ∧ Nontrivial (F.H n)}

theorem exactDetectionIndex_eq_zero_of_nonempty_closed {X : TopCat.{0}} {P : Set X}
    (hClosed : IsClosed P) (hNonempty : P.Nonempty) : exactDetectionIndex X P = 0 := by
  apply le_antisymm _ bot_le
  exact sInf_le ⟨0, rfl, supportSheaf X P, supportSheaf_support_eq hClosed,
    supportSheaf_H0_nontrivial hNonempty⟩

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``supportSheaf_support_eq, ``supportSheaf_H0_nontrivial,
      ``exactDetectionIndex_eq_zero_of_nonempty_closed] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.ExactSupportDetection
