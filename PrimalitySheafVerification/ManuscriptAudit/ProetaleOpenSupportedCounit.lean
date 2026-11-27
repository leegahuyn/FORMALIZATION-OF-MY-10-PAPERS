import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedSupportLocalConstants
import PrimalitySheafVerification.ManuscriptAudit.DownwardClosedLanCounit
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension

/-! A native pro-étale sheaf whose sections are locally zero off an open is
recovered by extending its restriction by zero. -/

namespace ManuscriptAudit.ProetaleOpenSupportedCounit

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension
open ProetaleClosedSupportLocalConstants (openObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev P := proetalePostcompose j
private abbrev L := (P j).op

variable (F : Sheaf (Scheme.ProEt.topology X) A)

local instance postFull : (P j).Full := (postcomposeFullyFaithful j).full
local instance postFaithful : (P j).Faithful := (postcomposeFullyFaithful j).faithful
local instance hasLan (F : Y.ProEtᵒᵖ ⥤ A) : (L j).HasLeftKanExtension F :=
  hasLeftKanExtension j A F
local instance hasPointwise (F : Y.ProEtᵒᵖ ⥤ A) : (L j).HasPointwiseLeftKanExtension F :=
  hasPointwiseLeftKanExtension j A F

private abbrev raw :=
  DownwardClosedLanCounit.counit (L j) F.obj

private theorem chart_in_image (W : X.ProEt) (h : Set.range W.hom ⊆ Set.range j) :
    ∃ V : Y.ProEt, Nonempty ((P j).obj V ≅ W) := by
  let g := IsOpenImmersion.lift j W.hom h
  have hg : g ≫ j = W.hom := IsOpenImmersion.lift_fac _ _ _
  letI : WeaklyEtale (g ≫ j) := hg.symm ▸ W.prop
  let V := MorphismProperty.Over.mk ⊤ g (WeaklyEtale.of_comp g j)
  refine ⟨V, ⟨MorphismProperty.Over.isoMk (Iso.refl W.left) ?_⟩⟩
  change 𝟙 W.left ≫ W.hom = g ≫ j
  rw [Category.id_comp, hg]

private theorem downward_closed (W : X.ProEtᵒᵖ) (a : CostructuredArrow (L j) W) :
    ∃ V : Y.ProEtᵒᵖ, Nonempty ((L j).obj V ≅ W) := by
  let f : W.unop ⟶ (P j).obj a.left.unop := a.hom.unop
  have hf : f.left ≫ a.left.unop.hom ≫ j = W.unop.hom := MorphismProperty.Over.w f
  have hRange : Set.range W.unop.hom ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    refine ⟨a.left.unop.hom (f.left x), ?_⟩
    exact congrArg (fun g : W.unop.left ⟶ X ↦ g x) hf
  obtain ⟨V, ⟨e⟩⟩ := chart_in_image j W.unop hRange
  exact ⟨op V, ⟨e.op.symm⟩⟩

private theorem raw_mono_on_sections (U : X.ProEtᵒᵖ) : Mono ((raw j F).app U) :=
  DownwardClosedLanCounit.counit_component_mono (L j) F.obj (downward_closed j) U

private theorem raw_locallyInjective :
    Presheaf.IsLocallyInjective (J (X := X)) (raw j F) where
  equalizerSieve_mem {U} a b hb := by
    have hd := (AddCommGrpCat.mono_iff_injective _).mp (raw_mono_on_sections j F U) hb
    subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact J.top_mem _

/-- Sections are supported on the open if they are locally zero at every point
outside that open, and can otherwise be restricted to an open chart in it. -/
def LocallySupported : Prop :=
  ∀ (U : X.ProEt) (s : F.obj.obj (op U)) (x : U.left),
    ∃ W : U.left.Opens, x ∈ W ∧
      (Set.range (openObject U W).hom ⊆ Set.range j ∨ F.obj.map (openArrow U W).op s = 0)

set_option maxHeartbeats 1700000 in
private theorem raw_locallySurjective (h : LocallySupported j F) :
    Presheaf.IsLocallySurjective (J (X := X)) (raw j F) where
  imageSieve_mem {U} s := by
    classical
    choose W hW hw using fun x : U.left ↦ h U s x
    let V (x : U.left) := openObject U (W x)
    let f (x : U.left) : V x ⟶ U := openArrow U (W x)
    have hCover : Sieve.ofArrows V f ∈ J (X := X) U := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows V f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage U.left
      rw [Presieve.map_ofArrows]
      apply Scheme.etalePrecoverage_le_proetalePrecoverage _
      change Presieve.ofArrows (fun x ↦ (W x).toScheme) (fun x ↦ (W x).ι) ∈
        Scheme.precoverage @Etale U.left
      exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
        ⟨fun x ↦ ⟨x, ⟨x, hW x⟩, rfl⟩, fun _ ↦ inferInstance⟩
    apply (J (X := X)).superset_covering _ hCover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨x⟩
    rcases hw x with hx | hx
    · obtain ⟨V', ⟨e⟩⟩ := chart_in_image j (V x) hx
      letI : IsIso ((raw j F).app (op (V x))) :=
        DownwardClosedLanCounit.counit_at_iso_isIso (L j) F.obj e.op.symm
      exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
        (F.obj.map (f x).op s)
    · refine ⟨0, ?_⟩
      change (raw j F).app (op (V x)) 0 = F.obj.map (f x).op s
      rw [map_zero, hx]

/-- The actual sheafified Kan counit recovers a locally supported native sheaf. -/
def extensionRestrictionIso (h : LocallySupported j F) :
    (extensionByZero j A).obj ((restriction j A).obj F) ≅ F := by
  let Q := presheafToSheaf (J (X := X)) A
  letI := raw_locallyInjective j F
  letI := raw_locallySurjective j F h
  letI : IsIso (Q.map (raw j F)) :=
    ((J (X := X)).W_iff (raw j F)).mp ((J (X := X)).W_of_isLocallyBijective (raw j F))
  exact asIso (Q.map (raw j F)) ≪≫ (sheafificationIso F).symm

end
end ManuscriptAudit.ProetaleOpenSupportedCounit

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleOpenSupportedCounit.extensionRestrictionIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
