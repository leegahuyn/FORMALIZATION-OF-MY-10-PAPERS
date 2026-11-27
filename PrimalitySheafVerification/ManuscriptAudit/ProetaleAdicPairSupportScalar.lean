import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.ProetaleAdicClosedPairSupport
import PrimalitySheafVerification.ManuscriptAudit.NativeAdicScalarAction

/-! Scalar multiplication on the actual two-point continuous adic support
kernel, and compatibility of its native cohomology map to the ambient scheme. -/

namespace ManuscriptAudit.ProetaleAdicPairSupportScalar

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open ProetaleContinuousDirectImageMaps (functions functionsOver diagonal)
open ProetaleContinuousCoefficientNaturality (mapOver diagonal_natural)
open ProetaleAdicClosedPairSupport (boundary pairRestriction support inclusion)
open NativeAdicScalarAction (multiply multiply_continuous scalarMap adicModule
  scalarMap_zero scalarMap_one scalarMap_add scalarMap_mul)

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X Z₀ Z₁ : Scheme.{0}} (i₀ : Z₀ ⟶ X) (i₁ : Z₁ ⟶ X)
variable (ℓ : ℕ) [Fact ℓ.Prime]

private abbrev A := AddCommGrpCat.{1}
private abbrev G := boundary i₀ i₁ ℓ
private abbrev d := pairRestriction i₀ i₁ ℓ
private abbrev I := inclusion i₀ i₁ ℓ
private abbrev P := support i₀ i₁ ℓ

private def boundaryScalar (r : ℤ_[ℓ]) : G i₀ i₁ ℓ ⟶ G i₀ i₁ ℓ :=
  prod.map (mapOver (multiply ℓ r) (multiply_continuous ℓ r) i₀)
    (mapOver (multiply ℓ r) (multiply_continuous ℓ r) i₁)

private theorem scalar_square (r : ℤ_[ℓ]) :
    scalarMap X ℓ r ≫ d i₀ i₁ ℓ = d i₀ i₁ ℓ ≫ boundaryScalar i₀ i₁ ℓ r := by
  let m₀ := mapOver (multiply ℓ r) (multiply_continuous ℓ r) i₀
  let m₁ := mapOver (multiply ℓ r) (multiply_continuous ℓ r) i₁
  apply prod.hom_ext
  · change (scalarMap X ℓ r ≫ d i₀ i₁ ℓ) ≫ prod.fst =
      (d i₀ i₁ ℓ ≫ prod.map m₀ m₁) ≫ prod.fst
    simp only [Category.assoc, prod.map_fst]
    rw [← Category.assoc (d i₀ i₁ ℓ) prod.fst m₀,
      show d i₀ i₁ ℓ ≫ prod.fst = diagonal ℤ_[ℓ] i₀ from prod.lift_fst _ _]
    exact diagonal_natural (multiply ℓ r) (multiply_continuous ℓ r) i₀
  · change (scalarMap X ℓ r ≫ d i₀ i₁ ℓ) ≫ prod.snd =
      (d i₀ i₁ ℓ ≫ prod.map m₀ m₁) ≫ prod.snd
    simp only [Category.assoc, prod.map_snd]
    rw [← Category.assoc (d i₀ i₁ ℓ) prod.snd m₁,
      show d i₀ i₁ ℓ ≫ prod.snd = diagonal ℤ_[ℓ] i₁ from prod.lift_snd _ _]
    exact diagonal_natural (multiply ℓ r) (multiply_continuous ℓ r) i₁

/-- Literal multiplication on the two-boundary support kernel sheaf. -/
def scalar (r : ℤ_[ℓ]) : P i₀ i₁ ℓ ⟶ P i₀ i₁ ℓ :=
  kernel.lift (d i₀ i₁ ℓ) (I i₀ i₁ ℓ ≫ scalarMap X ℓ r) (by
    rw [Category.assoc, scalar_square, ← Category.assoc, kernel.condition, zero_comp])

@[reassoc]
theorem scalar_inclusion (r : ℤ_[ℓ]) :
    scalar i₀ i₁ ℓ r ≫ I i₀ i₁ ℓ = I i₀ i₁ ℓ ≫ scalarMap X ℓ r :=
  kernel.lift_ι _ _ _

private theorem scalar_zero : scalar i₀ i₁ ℓ 0 = 0 := by
  apply (cancel_mono (I i₀ i₁ ℓ)).mp
  rw [scalar_inclusion, scalarMap_zero, comp_zero, zero_comp]

private theorem scalar_one : scalar i₀ i₁ ℓ 1 = 𝟙 _ := by
  apply (cancel_mono (I i₀ i₁ ℓ)).mp
  rw [scalar_inclusion, scalarMap_one, Category.comp_id, Category.id_comp]

private theorem scalar_add (a b : ℤ_[ℓ]) :
    scalar i₀ i₁ ℓ (a + b) = scalar i₀ i₁ ℓ a + scalar i₀ i₁ ℓ b := by
  apply (cancel_mono (I i₀ i₁ ℓ)).mp
  simp only [scalar_inclusion, scalarMap_add, Preadditive.comp_add, Preadditive.add_comp]

private theorem scalar_mul (a b : ℤ_[ℓ]) :
    scalar i₀ i₁ ℓ (a * b) = scalar i₀ i₁ ℓ b ≫ scalar i₀ i₁ ℓ a := by
  apply (cancel_mono (I i₀ i₁ ℓ)).mp
  simp only [scalar_inclusion, scalarMap_mul, Category.assoc, scalar_inclusion_assoc]

/-- The genuine cohomology of the support kernel has its native adic scalar action. -/
def supportModule (n : ℕ) : Module ℤ_[ℓ] (Sheaf.H (P i₀ i₁ ℓ) n) where
  smul a := Sheaf.H.map (scalar i₀ i₁ ℓ a) n
  one_smul x := by
    change Sheaf.H.map (scalar i₀ i₁ ℓ 1) n x = x
    rw [scalar_one, Sheaf.H.map_id_apply]
  mul_smul a b x := by
    change Sheaf.H.map (scalar i₀ i₁ ℓ (a * b)) n x =
      Sheaf.H.map (scalar i₀ i₁ ℓ a) n (Sheaf.H.map (scalar i₀ i₁ ℓ b) n x)
    rw [scalar_mul, Sheaf.H.map_comp_apply]
  smul_zero a := map_zero (Sheaf.H.map (scalar i₀ i₁ ℓ a) n)
  smul_add a := map_add (Sheaf.H.map (scalar i₀ i₁ ℓ a) n)
  add_smul a b x := by
    change Sheaf.H.map (scalar i₀ i₁ ℓ (a + b)) n x =
      Sheaf.H.map (scalar i₀ i₁ ℓ a) n x + Sheaf.H.map (scalar i₀ i₁ ℓ b) n x
    rw [scalar_add, Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (scalar i₀ i₁ ℓ 0) n x = 0
    rw [scalar_zero]
    simp [Sheaf.H.map_apply]

/-- The actual morphism from support cohomology to ambient cohomology is adic-linear. -/
def inclusionLinear (n : ℕ) :
    letI := supportModule i₀ i₁ ℓ n
    letI := adicModule X ℓ n
    Sheaf.H (P i₀ i₁ ℓ) n →ₗ[ℤ_[ℓ]] X.EllAdicCohomology ℓ n := by
  letI := supportModule i₀ i₁ ℓ n
  letI := adicModule X ℓ n
  refine { (Sheaf.H.map (I i₀ i₁ ℓ) n) with map_smul' := fun r x ↦ ?_ }
  change Sheaf.H.map (I i₀ i₁ ℓ) n (Sheaf.H.map (scalar i₀ i₁ ℓ r) n x) =
    Sheaf.H.map (scalarMap X ℓ r) n (Sheaf.H.map (I i₀ i₁ ℓ) n x)
  rw [← Sheaf.H.map_comp_apply, scalar_inclusion, Sheaf.H.map_comp_apply]

end
end ManuscriptAudit.ProetaleAdicPairSupportScalar

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.ProetaleAdicPairSupportScalar.supportModule,
      ``ManuscriptAudit.ProetaleAdicPairSupportScalar.inclusionLinear] do
    let dependencies ← collectAxioms name
    let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
    unless unexpected.isEmpty do
      throwError m!"{name} depends on unexpected axioms {unexpected}"
    logInfo m!"{name} uses {dependencies}"
