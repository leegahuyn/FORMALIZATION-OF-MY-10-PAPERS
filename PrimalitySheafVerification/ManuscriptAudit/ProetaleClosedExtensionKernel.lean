import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleClosedKernelLocalSupport
import PrimalitySheafVerification.ManuscriptAudit.DownwardClosedLanCounit
import PrimalitySheafVerification.ManuscriptAudit.OpenProetaleExtension

/-! For discrete coefficients the actual extension by zero of the
restricted support kernel agrees with the support kernel. -/

namespace ManuscriptAudit.ProetaleClosedExtensionKernel

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open OpenProetaleExtension
open ProetaleClosedKernelLocalSupport (K locally_open_or_zero)
open ProetaleClosedSupportLocalConstants (openObject openArrow)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z Y : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i]
  (j : Y ⟶ X) [IsOpenImmersion j]
variable (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev A := AddCommGrpCat.{1}
private abbrev J := Scheme.ProEt.topology X
private abbrev P := proetalePostcompose j
private abbrev L := (P j).op

local instance postFull : (P j).Full := (postcomposeFullyFaithful j).full
local instance postFaithful : (P j).Faithful := (postcomposeFullyFaithful j).faithful
local instance hasLan (F : Y.ProEtᵒᵖ ⥤ A) : (L j).HasLeftKanExtension F :=
  hasLeftKanExtension j A F
local instance hasPointwise (F : Y.ProEtᵒᵖ ⥤ A) : (L j).HasPointwiseLeftKanExtension F :=
  hasPointwiseLeftKanExtension j A F

private abbrev raw :=
  DownwardClosedLanCounit.counit (L j) (K i M).obj

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

private theorem raw_mono_on_sections (U : X.ProEtᵒᵖ) : Mono ((raw i j M).app U) :=
  DownwardClosedLanCounit.counit_component_mono (L j) (K i M).obj (downward_closed j) U

private theorem raw_locallyInjective :
    Presheaf.IsLocallyInjective (J (X := X)) (raw i j M) where
  equalizerSieve_mem {U} a b hb := by
    have hd := (AddCommGrpCat.mono_iff_injective _).mp (raw_mono_on_sections i j M U) hb
    subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact J.top_mem _

set_option maxHeartbeats 1700000 in
private theorem raw_locallySurjective (hComplement : Set.range j = (Set.range i)ᶜ) :
    Presheaf.IsLocallySurjective (J (X := X)) (raw i j M) where
  imageSieve_mem {U} s := by
    classical
    choose W hW hw using fun x : U.left ↦ locally_open_or_zero i j M hComplement U s x
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
      letI : IsIso ((raw i j M).app (op (V x))) :=
        DownwardClosedLanCounit.counit_at_iso_isIso (L j) (K i M).obj e.op.symm
      exact (AddCommGrpCat.epi_iff_surjective _).mp inferInstance
        ((K i M).obj.map (f x).op s)
    · refine ⟨0, ?_⟩
      change (raw i j M).app (op (V x)) 0 = (K i M).obj.map (f x).op s
      rw [map_zero, hx]

/-- The supported native sheaf is the actual extension by zero of its
open restriction. The comparison is the sheafified Kan counit. -/
def extensionKernelIso (hComplement : Set.range j = (Set.range i)ᶜ) :
    (extensionByZero j A).obj ((restriction j A).obj (K i M)) ≅ K i M := by
  let Q := presheafToSheaf (J (X := X)) A
  letI := raw_locallyInjective i j M
  letI := raw_locallySurjective i j M hComplement
  letI : IsIso (Q.map (raw i j M)) :=
    ((J (X := X)).W_iff Q).mp ((J (X := X)).W_of_isLocallyBijective (raw i j M))
  exact asIso (Q.map (raw i j M)) ≪≫ (sheafificationIso (K i M)).symm

end
end ManuscriptAudit.ProetaleClosedExtensionKernel

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.ProetaleClosedExtensionKernel.extensionKernelIso
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
