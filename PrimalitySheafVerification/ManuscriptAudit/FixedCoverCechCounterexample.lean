import Lean.Util.CollectAxioms
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import Mathlib.CategoryTheory.Adjunction.Whiskering
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Sites.LeftExact
import Mathlib.RingTheory.Ideal.Int
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.Tactic.NormNum
import PrimalitySheafVerification.ManuscriptAudit.TwoOpenDerivedComparison

/-!
Paper 4, physical p. 114, Proposition 3.19(iii) asserts that the natural
comparison is an isomorphism through degree one on finite principal-open
covers. For one abelian sheaf on Spec ℤ, the fixed cover D(2), D(3)
has zero Čech H¹, while the native degree-one sheaf cohomology of
Spec ℤ is nonzero. The same sheaf gives a degree-zero obstruction to
the shrinking statement in Proposition 3.19(ii): its restrictions
are compatible with common coefficient embeddings on nonempty opens,
but D(35) has sections that do not extend to Spec ℤ.
-/

namespace ManuscriptAudit.FixedCoverCechCounterexample

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open ManuscriptAudit.TwoOpenDerivedComparison
open scoped ZeroObject

noncomputable section

set_option synthInstance.maxHeartbeats 120000
set_option maxHeartbeats 1200000

local notation "X" => TopCat.of (PrimeSpectrum ℤ)
private abbrev G := AddCommGrpCat.{0}
local notation "J" => Opens.grothendieckTopology (PrimeSpectrum ℤ)
local notation "A" => AddCommGrpCat.of (ZMod 2)
local notation "D" => PrimeSpectrum.basicOpen (R := ℤ)

private instance : Fact (1 < (2 : ℕ)) := ⟨by decide⟩
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def genericPoint : X := ⟨⊥, inferInstance⟩

private theorem generic_specializes (p : X) : Specializes genericPoint p :=
  (PrimeSpectrum.le_iff_specializes genericPoint p).mp (show (⊥ : Ideal ℤ) ≤ p.asIdeal from bot_le)

private def closedPoint (p : ℕ) [Fact p.Prime] : X :=
  ⟨Ideal.span ({(p : ℤ)} : Set ℤ), (Int.ideal_span_isMaximal_of_prime p).isPrime⟩

private theorem closedPoint_mem_basicOpen (p : ℕ) [Fact p.Prime] (m : ℤ) :
    closedPoint p ∈ D m ↔ ¬ (p : ℤ) ∣ m := by
  change m ∉ Ideal.span ({(p : ℤ)} : Set ℤ) ↔ _
  rw [Ideal.mem_span_singleton]

private theorem generic_mem_basicOpen {m : ℤ} (hm : m ≠ 0) : genericPoint ∈ D m := by
  change m ∉ (⊥ : Ideal ℤ)
  simpa using hm

private def sky (p : X) : Sheaf J G := by
  classical
  exact skyscraperSheaf p A

private theorem sky_obj_of_mem {p : X} {U : (Opens X)ᵒᵖ} (hp : p ∈ unop U) :
    (sky p).obj.obj U = A := by
  classical
  change (if p ∈ unop U then A else terminal G) = A
  rw [if_pos hp]

private def sky_obj_isTerminal {p : X} {U : (Opens X)ᵒᵖ} (hp : p ∉ unop U) :
    IsTerminal ((sky p).obj.obj U) := by
  classical
  have heq : (sky p).obj.obj U = terminal G := by
    change (if p ∈ unop U then A else terminal G) = _
    rw [if_neg hp]
  exact heq.symm ▸ terminalIsTerminal

private def skyMapApp {p q : X} (h : Specializes p q) (U : (Opens X)ᵒᵖ) :
    (sky p).obj.obj U ⟶ (sky q).obj.obj U := by
  classical
  exact if hq : q ∈ unop U then
    eqToHom ((sky_obj_of_mem (h.mem_open (unop U).isOpen hq)).trans
      (sky_obj_of_mem hq).symm)
  else 0

private theorem sky_map_of_target_mem {p : X} {U V : (Opens X)ᵒᵖ} (f : U ⟶ V)
    (hp : p ∈ unop V) :
    (sky p).obj.map f = eqToHom ((sky_obj_of_mem (f.unop.le hp)).trans
      (sky_obj_of_mem hp).symm) := by
  classical
  change (skyscraperPresheaf p A).map f = _
  rw [skyscraperPresheaf_map, dif_pos hp]
  rfl

private def skyMap {p q : X} (h : Specializes p q) : sky p ⟶ sky q :=
  ObjectProperty.homMk
    { app := skyMapApp h
      naturality := by
        intro U V f
        classical
        by_cases hq : q ∈ unop V
        · have hqU : q ∈ unop U := f.unop.le hq
          have hp : p ∈ unop V := h.mem_open (unop V).isOpen hq
          rw [sky_map_of_target_mem f hp, sky_map_of_target_mem f hq]
          simp only [skyMapApp, hq, hqU, ↓reduceDIte, eqToHom_trans]
        · exact (sky_obj_isTerminal hq).hom_ext _ _ }

private def ev (U : Opens X) : Sheaf J G ⥤ G :=
  sheafToPresheaf J G ⋙ (evaluation _ G).obj (op U)

private instance (U : Opens X) : PreservesLimits (ev U) := by
  unfold ev
  infer_instance

private instance (U : Opens X) : (ev U).PreservesZeroMorphisms := by
  unfold ev
  infer_instance

private def closedMap (p : X) : sky genericPoint ⟶ sky p :=
  skyMap (generic_specializes p)

private theorem isIso_eval_closedMap {p : X} {U : Opens X} (hp : p ∈ U) :
    IsIso ((ev U).map (closedMap p)) := by
  classical
  change IsIso (skyMapApp (generic_specializes p) (op U))
  unfold skyMapApp
  rw [dif_pos hp]
  infer_instance

private def diagonalToClosedPair (p q : X) :
    sky genericPoint ⟶ sky p ⨯ sky q :=
  prod.lift (closedMap p) (closedMap q)

/-- The kernel of the map from the generic skyscraper to the two closed
skyscrapers at (5) and (7). -/
def boundarySheaf : Sheaf J G :=
  kernel (diagonalToClosedPair (closedPoint 5) (closedPoint 7))

private theorem eval_diagonal_fst (p q : X) (U : Opens X) :
    (ev U).map (diagonalToClosedPair p q) ≫ (ev U).map prod.fst =
      (ev U).map (closedMap p) := by
  rw [← Functor.map_comp, diagonalToClosedPair, prod.lift_fst]

private theorem eval_diagonal_snd (p q : X) (U : Opens X) :
    (ev U).map (diagonalToClosedPair p q) ≫ (ev U).map prod.snd =
      (ev U).map (closedMap q) := by
  rw [← Functor.map_comp, diagonalToClosedPair, prod.lift_snd]

private theorem eval_kernel_subsingleton {p q : X} {U : Opens X} (h : p ∈ U ∨ q ∈ U) :
    Subsingleton ((ev U).obj (kernel (diagonalToClosedPair p q))) := by
  let g := (ev U).map (diagonalToClosedPair p q)
  have hg : Mono g := by
    constructor
    intro W s t he
    rcases h with hp | hq
    · letI := isIso_eval_closedMap hp
      apply (cancel_mono ((ev U).map (closedMap p))).mp
      rw [← eval_diagonal_fst p q U, ← Category.assoc, ← Category.assoc, he]
    · letI := isIso_eval_closedMap hq
      apply (cancel_mono ((ev U).map (closedMap q))).mp
      rw [← eval_diagonal_snd p q U, ← Category.assoc, ← Category.assoc, he]
  letI := hg
  have hz : IsZero (kernel g) :=
    (isZero_zero G).of_iso (kernel.ofMono g)
  exact AddCommGrpCat.subsingleton_of_isZero
    (hz.of_iso (PreservesKernel.iso (ev U) (diagonalToClosedPair p q)))

private def eval_kernel_iso_of_outside {p q : X} {U : Opens X}
    (hp : p ∉ U) (hq : q ∉ U) (hg : genericPoint ∈ U) :
    (ev U).obj (kernel (diagonalToClosedPair p q)) ≅ A := by
  let e := PreservesLimitPair.iso (ev U) (sky p) (sky q)
  have hZero : (ev U).map (diagonalToClosedPair p q) = 0 := by
    apply (cancel_mono e.hom).mp
    apply prod.hom_ext
    · rw [zero_comp, zero_comp, Category.assoc, PreservesLimitPair.iso_hom,
        prodComparison_fst, eval_diagonal_fst]
      exact (sky_obj_isTerminal hp).hom_ext _ _
    · rw [zero_comp, zero_comp, Category.assoc, PreservesLimitPair.iso_hom,
        prodComparison_snd, eval_diagonal_snd]
      exact (sky_obj_isTerminal hq).hom_ext _ _
  exact (PreservesKernel.iso (ev U) (diagonalToClosedPair p q)).trans
    ((kernelIsoOfEq hZero).trans (kernelZeroIsoSource.trans (eqToIso (sky_obj_of_mem hg))))

private theorem basicOpen_sup_eq_top_of_isCoprime {m n : ℤ} (h : IsCoprime m n) :
    D m ⊔ D n = (⊤ : Opens X) := by
  obtain ⟨a, b, hab⟩ := h
  apply top_unique
  intro P _
  change m ∉ P.asIdeal ∨ n ∉ P.asIdeal
  by_cases hm : m ∈ P.asIdeal
  · right
    intro hn
    apply P.2.ne_top
    apply (Ideal.eq_top_iff_one _).mpr
    rw [← hab]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left a hm) (P.asIdeal.mul_mem_left b hn)
  · exact Or.inl hm

theorem cover_D2_D3 : D 2 ⊔ D 3 = (⊤ : Opens X) :=
  basicOpen_sup_eq_top_of_isCoprime ⟨-1, 1, by norm_num⟩

theorem cover_D5_D7 : D 5 ⊔ D 7 = (⊤ : Opens X) :=
  basicOpen_sup_eq_top_of_isCoprime ⟨3, -2, by norm_num⟩

private theorem sections_subsingleton_of_five_or_seven {U : Opens X}
    (h : closedPoint 5 ∈ U ∨ closedPoint 7 ∈ U) :
    Subsingleton (boundarySheaf.obj.obj (op U)) :=
  eval_kernel_subsingleton h

private def overlap_57_sections_iso :
    boundarySheaf.obj.obj (op (D 5 ⊓ D 7)) ≅ A := by
  apply eval_kernel_iso_of_outside
  · rintro ⟨h, _⟩
    exact (closedPoint_mem_basicOpen 5 5).mp h (by norm_num)
  · rintro ⟨_, h⟩
    exact (closedPoint_mem_basicOpen 7 7).mp h (by norm_num)
  · exact ⟨generic_mem_basicOpen (by norm_num), generic_mem_basicOpen (by norm_num)⟩


private def boundaryInclusion : boundarySheaf ⟶ sky genericPoint :=
  kernel.ι (diagonalToClosedPair (closedPoint 5) (closedPoint 7))

/-- On a nonempty open, embed the boundary sections into the common
generic coefficient group. -/
def sectionsIntoCoefficients (U : Opens X) (hU : (U : Set X).Nonempty) :
    boundarySheaf.obj.obj (op U) ⟶ A :=
  boundaryInclusion.hom.app (op U) ≫
    eqToHom (sky_obj_of_mem (by
      obtain ⟨p, hp⟩ := hU
      exact (generic_specializes p).mem_open U.isOpen hp))

theorem sectionsIntoCoefficients_injective (U : Opens X) (hU : (U : Set X).Nonempty) :
    Function.Injective (sectionsIntoCoefficients U hU) := by
  let f := diagonalToClosedPair (closedPoint 5) (closedPoint 7)
  let e := PreservesKernel.iso (ev U) f
  have hEq : e.hom ≫ kernel.ι ((ev U).map f) = (ev U).map (kernel.ι f) := by
    apply (cancel_epi e.inv).mp
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    exact (PreservesKernel.iso_inv_ι (ev U) f).symm
  haveI : Mono ((ev U).map (kernel.ι f)) := by
    rw [← hEq]
    infer_instance
  have hInc : Function.Injective ((ev U).map (kernel.ι f)) :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  obtain ⟨p, hp⟩ := hU
  let hG : genericPoint ∈ U := (generic_specializes p).mem_open U.isOpen hp
  let i := eqToIso (sky_obj_of_mem (U := op U) hG)
  have hIso : Function.Injective i.hom := i.addCommGroupIsoToAddEquiv.injective
  intro a b hab
  change i.hom ((ev U).map (kernel.ι f) a) = i.hom ((ev U).map (kernel.ι f) b) at hab
  exact hInc (hIso hab)

/-- After embedding both section groups in the same coefficients,
restriction is the inclusion of their images. -/
theorem sectionRestriction_commutes_with_coefficients {U V : Opens X}
    (h : V ≤ U) (hV : (V : Set X).Nonempty) :
    boundarySheaf.obj.map (homOfLE h).op ≫ sectionsIntoCoefficients V hV =
      sectionsIntoCoefficients U (hV.mono h) := by
  dsimp only [sectionsIntoCoefficients]
  rw [← Category.assoc, boundaryInclusion.hom.naturality, Category.assoc]
  have hp : genericPoint ∈ V := by
    obtain ⟨p, hp⟩ := hV
    exact (generic_specializes p).mem_open V.isOpen hp
  rw [sky_map_of_target_mem (homOfLE h).op hp, eqToHom_trans]

theorem boundarySheaf_restriction_injective {U V : Opens X} (h : V ≤ U)
    (hV : (V : Set X).Nonempty) :
    Function.Injective (boundarySheaf.obj.map (homOfLE h).op) := by
  intro a b hab
  apply sectionsIntoCoefficients_injective U (hV.mono h)
  rw [← sectionRestriction_commutes_with_coefficients h hV]
  exact congrArg (fun c : boundarySheaf.obj.obj (op V) => sectionsIntoCoefficients V hV c) hab

theorem boundarySheaf_global_sections_subsingleton :
    Subsingleton (boundarySheaf.obj.obj (op (⊤ : Opens X))) :=
  sections_subsingleton_of_five_or_seven (Or.inl (by simp))

theorem boundarySheaf_D35_sections_nontrivial :
    Nontrivial (boundarySheaf.obj.obj (op (D 35))) := by
  have h : D 35 = D 5 ⊓ D 7 := PrimeSpectrum.basicOpen_mul (5 : ℤ) 7
  rw [h]
  exact overlap_57_sections_iso.symm.addCommGroupIsoToAddEquiv.injective.nontrivial

/-- Shrinking to D(35) creates a section even when all nonempty-open
restrictions are inclusions after the common coefficient embeddings. -/
theorem paper4_shrinking_creates_section_with_inclusions :
    ∃ s : boundarySheaf.obj.obj (op (D 35)),
      ∀ t : boundarySheaf.obj.obj (op (⊤ : Opens X)),
        (boundarySheaf.obj.map (homOfLE (le_top : D 35 ≤ (⊤ : Opens X))).op) t ≠ s := by
  letI := boundarySheaf_global_sections_subsingleton
  letI := boundarySheaf_D35_sections_nontrivial
  obtain ⟨s, hs⟩ := exists_ne (0 : boundarySheaf.obj.obj (op (D 35)))
  refine ⟨s, fun t h => hs ?_⟩
  rw [← h, Subsingleton.elim t 0, map_zero]

/-- The normalized two-open Čech H¹ of the fixed cover D(2), D(3) is zero. -/
theorem boundarySheaf_fixedCech_subsingleton :
    Subsingleton
      ((boundarySheaf.obj.obj (op (D 2 ⊓ D 3))) ⧸
        (twoOpenDifferential boundarySheaf.obj (D 2) (D 3)).range) := by
  letI : Subsingleton (boundarySheaf.obj.obj (op (D 2 ⊓ D 3))) :=
    sections_subsingleton_of_five_or_seven (Or.inl
      ⟨(closedPoint_mem_basicOpen 5 2).mpr (by decide),
       (closedPoint_mem_basicOpen 5 3).mpr (by decide)⟩)
  exact (QuotientAddGroup.mk'_surjective _).subsingleton

local instance : HasExt.{0} (Sheaf J G) :=
  IsGrothendieckAbelian.hasExt _

/-- In degree zero, the native Ext group from the free representable sheaf
is the usual group of sections. -/
private def degreeZeroEquiv (F : Sheaf J G) (U : Opens X) :
    F.H' 0 U ≃ F.obj.obj (op U) := by
  change Ext ((presheafToSheaf J G).obj (yoneda.obj U ⋙ AddCommGrpCat.free)) F 0 ≃ _
  refine Ext.addEquiv₀.toEquiv.trans ?_
  refine ((sheafificationAdjunction J G).homEquiv _ F).trans ?_
  refine ((Adjunction.whiskerRight (Opens X)ᵒᵖ AddCommGrpCat.adj).homEquiv _ F.obj).trans ?_
  exact yonedaEquiv

/-- The native derived H¹ on Spec ℤ is nonzero, as witnessed by the distinct
cover D(5), D(7) and its Mayer–Vietoris connecting map. -/
theorem boundarySheaf_derivedH1_nontrivial :
    Nontrivial (boundarySheaf.H' 1 (⊤ : Opens X)) := by
  let s := Opens.mayerVietorisSquare (D 5) (D 7)
  have hCover : s.X₄ = (⊤ : Opens X) := cover_D5_D7
  rw [← hCover]
  letI : Subsingleton (boundarySheaf.obj.obj (op s.X₂)) :=
    sections_subsingleton_of_five_or_seven (Or.inr
      ((closedPoint_mem_basicOpen 7 5).mpr (by decide)))
  letI : Subsingleton (boundarySheaf.obj.obj (op s.X₃)) :=
    sections_subsingleton_of_five_or_seven (Or.inl
      ((closedPoint_mem_basicOpen 5 7).mpr (by decide)))
  letI : Subsingleton (boundarySheaf.H' 0 s.X₂) :=
    (degreeZeroEquiv boundarySheaf s.X₂).injective.subsingleton
  letI : Subsingleton (boundarySheaf.H' 0 s.X₃) :=
    (degreeZeroEquiv boundarySheaf s.X₃).injective.subsingleton
  letI : Subsingleton ((boundarySheaf.H' 0 s.X₂ ⊞ boundarySheaf.H' 0 s.X₃ : AddCommGrpCat.{0})) :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.injective.subsingleton
  letI : Nontrivial (boundarySheaf.obj.obj (op s.X₁)) :=
    overlap_57_sections_iso.symm.addCommGroupIsoToAddEquiv.injective.nontrivial
  letI : Nontrivial (boundarySheaf.H' 0 s.X₁) :=
    (degreeZeroEquiv boundarySheaf s.X₁).symm.injective.nontrivial
  have hRange : (s.fromBiprod boundarySheaf 0).hom.range = ⊥ := by
    apply eq_bot_iff.mpr
    rintro z ⟨y, rfl⟩
    rw [Subsingleton.elim y 0, map_zero]
    exact AddSubgroup.zero_mem _
  letI : Nontrivial ((boundarySheaf.H' 0 s.X₁) ⧸ (s.fromBiprod boundarySheaf 0).hom.range) := by
    rw [hRange]
    exact (QuotientAddGroup.quotientBot (G := boundarySheaf.H' 0 s.X₁)).symm.injective.nontrivial
  let e := coker_equiv_derivedRestrictionKer s boundarySheaf
  letI : Nontrivial (s.toBiprod boundarySheaf 1).hom.ker := e.injective.nontrivial
  exact (show Function.Injective
      (fun x : (s.toBiprod boundarySheaf 1).hom.ker => (x : boundarySheaf.H' 1 s.X₄))
    from Subtype.val_injective).nontrivial

/-- The comparison claimed for all finite principal-open covers cannot
be an isomorphism for this fixed cover. -/
theorem paper4_fixedCoverCech_not_derivedH1 :
    ¬ Nonempty
      (((boundarySheaf.obj.obj (op (D 2 ⊓ D 3))) ⧸
        (twoOpenDifferential boundarySheaf.obj (D 2) (D 3)).range) ≃+
        boundarySheaf.H' 1 (⊤ : Opens X)) := by
  letI := boundarySheaf_fixedCech_subsingleton
  letI := boundarySheaf_derivedH1_nontrivial
  rintro ⟨e⟩
  obtain ⟨a, b, hab⟩ := exists_pair_ne (boundarySheaf.H' 1 (⊤ : Opens X))
  exact hab (e.symm.injective (Subsingleton.elim (e.symm a) (e.symm b)))

end

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``cover_D2_D3, ``cover_D5_D7,
      ``sectionsIntoCoefficients_injective, ``sectionRestriction_commutes_with_coefficients,
      ``boundarySheaf_restriction_injective, ``boundarySheaf_global_sections_subsingleton,
      ``boundarySheaf_D35_sections_nontrivial, ``paper4_shrinking_creates_section_with_inclusions,
      ``boundarySheaf_fixedCech_subsingleton, ``boundarySheaf_derivedH1_nontrivial,
      ``paper4_fixedCoverCech_not_derivedH1] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"

end ManuscriptAudit.FixedCoverCechCounterexample
