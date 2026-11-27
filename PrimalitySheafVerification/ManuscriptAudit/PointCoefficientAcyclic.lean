import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientUniversal
import PrimalitySheafVerification.ManuscriptAudit.PointCoefficientExact

/-!
# All-degree acyclicity of point coefficients

For an arbitrary set of chosen points, a simultaneous injective
embedding of the coefficient groups induces a short exact sequence
that is surjective on every open. Dimension shifting computes the
actual positive Zariski cohomology groups.
-/

namespace ManuscriptAudit.PointCoefficientAcyclic

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open PointCoefficientExact PointCoefficientUniversal ClosedSupportDetection

noncomputable section

private abbrev G := AddCommGrpCat.{0}

local instance (X : TopCat.{0}) : HasExt.{0} (AbelianSheaf X) :=
  IsGrothendieckAbelian.hasExt _

variable {X : TopCat.{0}} (P : Set X)

private theorem dimensionShift (Q : ShortComplex (AbelianSheaf X)) (hQ : Q.ShortExact)
    [Injective Q.X₂] (n : ℕ) (hSurj : Function.Surjective (Sheaf.H.map Q.g n)) :
    Subsingleton (Q.X₁.H (n + 1)) := by
  apply subsingleton_of_forall_eq 0
  intro x
  let Z := (constantSheaf (Opens.grothendieckTopology X) G).obj
    (G.of (ULift ℤ))
  change Ext Z Q.X₁ (n + 1) at x
  have hx : x.comp (Ext.mk₀ Q.f) (add_zero (n + 1)) = 0 := Ext.eq_zero_of_injective _
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ Z hQ x hx (show n + 1 = n + 1 by rfl)
  obtain ⟨z, hz⟩ := hSurj y
  change z.comp (Ext.mk₀ Q.g) (add_zero n) = y at hz
  change x = 0
  rw [← hy, ← hz, Ext.comp_assoc_of_second_deg_zero, ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

private theorem HZero_map_surjective (S : P → ShortComplex G) (hS : ∀ p, (S p).ShortExact) :
    Function.Surjective (Sheaf.H.map (coefficientSequence P S).g 0) := by
  let Q := coefficientSequence P S
  let t : IsTerminal (⊤ : Opens X) :=
    IsTerminal.ofUniqueHom (fun _ => homOfLE le_top) (fun _ _ => Subsingleton.elim _ _)
  intro x
  obtain ⟨v, hv⟩ := app_g_surjective P S hS (op (⊤ : Opens X)) ((Sheaf.H.equiv₀ Q.X₃ t) x)
  refine ⟨(Sheaf.H.equiv₀ Q.X₂ t).symm v, ?_⟩
  change Sheaf.H.map Q.g 0 ((Sheaf.H.equiv₀ Q.X₂ t).symm v) = x
  rw [Sheaf.H.equiv₀_symm_naturality, hv, AddEquiv.symm_apply_apply]

private theorem successor_of_surjective (A : P → G) (n : ℕ)
    (h : ∀ S : P → ShortComplex G, (∀ p, (S p).ShortExact) →
      Function.Surjective (Sheaf.H.map (coefficientSequence P S).g n)) :
    Subsingleton ((coefficientSheaf P A).H (n + 1)) := by
  let S (p : P) := ShortComplex.cokernelSequence (Injective.ι (A p))
  have hS (p : P) : (S p).ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact (Injective.ι (A p)))
      (inferInstanceAs (Mono (Injective.ι (A p))))
      (inferInstanceAs (Epi (cokernel.π (Injective.ι (A p)))))
  let Q := coefficientSequence P S
  letI : ∀ p : P, Injective (G.of ((S p).X₂ : Type)) :=
    fun p => inferInstanceAs (Injective (Injective.under (A p)))
  letI : Injective Q.X₂ := injective_of_coefficients P (fun p => ((S p).X₂ : Type))
  exact dimensionShift Q (coefficientSequence_shortExact P S hS) n (h S hS)

/-- Positive ordinary Zariski cohomology vanishes for any set of point coefficients. -/
theorem H_succ_subsingleton (A : P → G) (n : ℕ) :
    Subsingleton ((coefficientSheaf P A).H (n + 1)) := by
  induction n generalizing A with
  | zero => exact successor_of_surjective P A 0 (HZero_map_surjective P)
  | succ n ih =>
      apply successor_of_surjective P A (n + 1)
      intro S _ x
      have hx : Subsingleton ((coefficientSequence P S).X₃.H (n + 1)) :=
        ih (fun p => (S p).X₃)
      exact ⟨0, hx.elim _ _⟩

end
end ManuscriptAudit.PointCoefficientAcyclic

open Lean Elab Command in
run_cmd do
  let name := ``ManuscriptAudit.PointCoefficientAcyclic.H_succ_subsingleton
  let ax ← collectAxioms name
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let bad := ax.filter fun x => !allowed.contains x
  unless bad.isEmpty do
    throwError m!"{name} depends on unexpected axioms {bad}"
  logInfo m!"{name} uses {ax}"
