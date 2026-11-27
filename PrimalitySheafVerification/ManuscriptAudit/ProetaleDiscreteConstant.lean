import Lean.Util.CollectAxioms
import Mathlib.CategoryTheory.Sites.LocallyBijective
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicHOneDetection

/-! Native finite pro-étale residue coefficients are the actual
constant sheaves in the cohomology universe. -/

namespace ManuscriptAudit.ProetaleDiscreteConstant

open AlgebraicGeometry CategoryTheory Opposite
open ProetaleResidueSheaves (continuousCoefficients)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable (X : Scheme.{0}) (M : Type) [AddCommGroup M] [TopologicalSpace M]
  [DiscreteTopology M] [IsTopologicalAddGroup M]

private abbrev J := Scheme.ProEt.topology X
private abbrev G := AddCommGrpCat.{1}
private abbrev liftedContinuous :=
  (sheafCompose (J X) AddCommGrpCat.uliftFunctor.{1}).obj (continuousCoefficients X M)
private abbrev coefficient := AddCommGrpCat.of (ULift.{1} M)

private def constantToContinuous :
    (Functor.const X.ProEtᵒᵖ).obj (coefficient M) ⟶ (liftedContinuous X M).obj where
  app U := AddCommGrpCat.ofHom
    { toFun := fun a ↦ ⟨ContinuousMap.const U.unop.left a.down⟩
      map_zero' := by apply ULift.ext; exact ContinuousMap.ext (fun _ ↦ rfl)
      map_add' _ _ := by apply ULift.ext; exact ContinuousMap.ext (fun _ ↦ rfl) }
  naturality {U V} f := by
    apply AddCommGrpCat.ext
    intro a
    apply ULift.ext
    exact ContinuousMap.ext (fun _ ↦ rfl)

private theorem locallyInjective :
    Presheaf.IsLocallyInjective (J X) (constantToContinuous X M) where
  equalizerSieve_mem {U} a b h := by
    by_cases hn : Nonempty U.unop.left
    · obtain ⟨x⟩ := hn
      have hab : a = b := ULift.ext
        (congrArg (fun s : ULift.{1} (C(U.unop.left, M)) ↦ s.down x) h)
      subst b
      rw [Presheaf.equalizerSieve_self_eq_top]
      exact (J X).top_mem _
    · letI : IsEmpty U.unop.left := ⟨fun x ↦ hn ⟨x⟩⟩
      exact (J X).superset_covering bot_le (Scheme.ProEt.bot_mem_topology U.unop)

private theorem locallySurjective :
    Presheaf.IsLocallySurjective (J X) (constantToContinuous X M) where
  imageSieve_mem {U} s := by
    let a : C(U.left, M) := s.down
    let V (m : M) : U.left.Opens :=
      ⟨a ⁻¹' {m}, (isOpen_discrete _).preimage a.continuous⟩
    let T (m : M) : X.ProEt := Scheme.ProEt.mk ((V m).ι ≫ U.hom)
    let f (m : M) : T m ⟶ U := MorphismProperty.Over.homMk (V m).ι rfl
    have hCov : Sieve.ofArrows T f ∈ J X U := by
      apply Precoverage.generate_mem_toGrothendieck
      change (Presieve.ofArrows T f).map (Scheme.ProEt.forget X ⋙ Over.forget X) ∈
        Scheme.proetalePrecoverage U.left
      rw [Presieve.map_ofArrows]
      apply Scheme.etalePrecoverage_le_proetalePrecoverage _
      change Presieve.ofArrows (fun m ↦ (V m).toScheme) (fun m ↦ (V m).ι) ∈
        Scheme.precoverage @Etale U.left
      exact (Scheme.ofArrows_mem_precoverage_iff @Etale).mpr
        ⟨fun x ↦ ⟨a x, ⟨x, rfl⟩, rfl⟩, fun _ ↦ inferInstance⟩
    apply (J X).superset_covering _ hCov
    apply (Sieve.generate_le_iff _ _).2
    rintro _ _ ⟨m⟩
    refine ⟨⟨m⟩, ?_⟩
    apply ULift.ext
    apply ContinuousMap.ext
    intro w
    exact w.property.symm

/-- The genuine constant coefficient sheaf equals the actual continuous
sections into a discrete group in the native cohomology universe. -/
def constantIso :
    (constantSheaf (J X) G).obj (coefficient M) ≅ liftedContinuous X M := by
  let P := presheafToSheaf (J X) G
  letI := locallyInjective X M
  letI := locallySurjective X M
  letI : IsIso (P.map (constantToContinuous X M)) :=
    ((J X).W_iff _).mp ((J X).W_of_isLocallyBijective (constantToContinuous X M))
  exact asIso (P.map (constantToContinuous X M)) ≪≫
    (sheafificationIso (liftedContinuous X M)).symm

end

section Residue

local instance residueTopology (d : ℕ) : TopologicalSpace (ZMod d) := ⊥
local instance residueDiscrete (d : ℕ) : DiscreteTopology (ZMod d) := ⟨rfl⟩

/-- The finite coefficient in the actual adic reduction map is the
constant sheaf of the displayed cyclic group. -/
def nativeResidueIso (X : Scheme.{0}) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (constantSheaf (Scheme.ProEt.topology X) AddCommGrpCat.{1}).obj
      (AddCommGrpCat.of (ULift.{1} (ZMod (ℓ ^ n)))) ≅
        ProetaleAdicHOneDetection.finiteCoefficient X ℓ n :=
  constantIso X (ZMod (ℓ ^ n))

end Residue

end ManuscriptAudit.ProetaleDiscreteConstant

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleDiscreteConstant.constantIso,
      ``ManuscriptAudit.ProetaleDiscreteConstant.nativeResidueIso] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
