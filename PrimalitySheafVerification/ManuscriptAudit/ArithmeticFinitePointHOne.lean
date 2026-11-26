import Lean.Elab.Tactic.Omega
import Lean.Util.CollectAxioms
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.LinearCombination
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleCuspHOne
import PrimalitySheafVerification.ManuscriptAudit.CuspRootCoefficients
import PrimalitySheafVerification.ManuscriptAudit.SmallEtaleCohomologyComparison

/-!
# Ordinary étale H¹ at any finite-field point of odd characteristic

Kummer identifies the degree-one class group with the square
classes of units. A finite field has cyclic units with two square
classes in odd characteristic, so the native small étale H¹ of
the point is ZMod 2.
-/

namespace ManuscriptAudit.ArithmeticFinitePointHOne

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian
open KummerAffineCohomology SmallEtaleCohomologyComparison

noncomputable section

variable (K : Type) [Field K] [Finite K] [hChar : Fact (ringChar K ≠ 2)]

private abbrev R := CommRingCat.of K
private abbrev J := Scheme.AffineEtale.topology (Spec (R K))
private abbrev cyclic := AddCommGrpCat.of (ZMod 2)

attribute [local instance] KummerCohomologySequence.affineSiteHasExt fullSiteHasExt

private theorem primitiveNegOne : IsPrimitiveRoot (-1 : K) 2 := by
  letI := ringChar.spec K
  exact IsPrimitiveRoot.neg_one (ringChar K) hChar.out

local instance : HasEnoughRootsOfUnity K 2 where
  prim := ⟨-1, primitiveNegOne K⟩
  cyc := rootsOfUnity.isCyclic K 2

private abbrev HR :=
  Sheaf.H ((constantSheaf (J K) AddCommGrpCat.{0}).obj
    (KummerConstantCoefficients.coefficientGroup K 2)) 1

private theorem two_isUnit : IsUnit ((2 : ℕ) : R K) := by
  apply isUnit_iff_ne_zero.mpr
  intro hz
  have h : (2 : K) = 0 := hz
  have hn : (-1 : K) - 1 = 0 := by linear_combination -h
  exact (Ring.neg_one_ne_one_of_char_ne_two hChar.out) (sub_eq_zero.mp hn)

local instance two_neZero : NeZero ((2 : ℕ) : K) :=
  ⟨isUnit_iff_ne_zero.mp (two_isUnit K)⟩

private def boundary : Additive Kˣ →+ HR K :=
  unitBoundary (K := K) (R K) 2 (by decide) (two_isUnit K)

private theorem boundary_square_zero (u : Kˣ) :
    boundary K (Additive.ofMul (u ^ (2 : ℕ))) = 0 :=
  (unitBoundary_eq_zero_iff (K := K) (R K) 2 (by decide) (two_isUnit K) _).mpr
    ⟨u, rfl⟩

private theorem exists_nonzero_boundary :
    ∃ v : HR K, v ≠ 0 := by
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := K) hChar.out
  have ha₀ : a ≠ 0 := by
    intro h
    subst a
    exact ha ⟨0, by simp⟩
  let u := Units.mk0 a ha₀
  refine ⟨boundary K (Additive.ofMul u), ?_⟩
  intro h
  obtain ⟨w, hw⟩ :=
    (unitBoundary_eq_zero_iff (K := K) (R K) 2 (by decide) (two_isUnit K) _).mp h
  apply ha
  refine ⟨(w : K), ?_⟩
  have hw' : (w : K) ^ (2 : ℕ) = a := by
    simpa [u] using congrArg (fun v : Kˣ => (v : K)) hw
  simpa [pow_two] using hw'.symm

private theorem roots_classes (g : Kˣ) (hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g)
    (v : HR K) :
    v = 0 ∨ v = boundary K (Additive.ofMul g) := by
  obtain ⟨a, rfl⟩ := unitBoundary_surjective_of_unitHOne (K := K)
    (R K) 2 (by decide) (two_isUnit K)
    (AffineEtaleCuspHOne.unitSheaf_HOne_subsingleton_of_pid K) v
  obtain ⟨n, hn⟩ : a.toMul ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    exact hg a.toMul
  let b := boundary K (Additive.ofMul g)
  have ha : a = n • Additive.ofMul g := Additive.ext hn.symm
  have hTwo : (2 : ℕ) • b = 0 := by
    change (2 : ℕ) • boundary K (Additive.ofMul g) = 0
    rw [← map_nsmul]
    exact boundary_square_zero K g
  change boundary K a = 0 ∨ boundary K a = b
  rw [ha, map_nsmul]
  have hReduce : n • b = (n % 2) • b := by
    calc
      n • b = (n % 2 + 2 * (n / 2)) • b :=
        congrArg (fun d : ℕ => d • b) (Nat.mod_add_div n 2).symm
      _ = _ := by
        rw [add_nsmul, mul_nsmul, hTwo, smul_zero, add_zero]
  change n • b = 0 ∨ n • b = b
  rw [hReduce]
  have hp : n % 2 = 0 ∨ n % 2 = 1 := by omega
  rcases hp with h | h
  · exact Or.inl (by rw [h, zero_nsmul])
  · exact Or.inr (by rw [h, one_nsmul])

/-- Native full small-étale H¹ of the odd finite-field point is cyclic of order two. -/
def finitePointCyclicHOneEquiv : ZMod 2 ≃+
    Sheaf.H ((constantSheaf (Spec (R K)).smallEtaleTopology AddCommGrpCat.{0}).obj cyclic) 1 := by
  let g : Kˣ := Classical.choose (IsCyclic.exists_generator (α := Kˣ))
  have hg : ∀ x : Kˣ, x ∈ Subgroup.zpowers g :=
    Classical.choose_spec (IsCyclic.exists_generator (α := Kˣ))
  let b := boundary K (Additive.ofMul g)
  have hb : b ≠ 0 := by
    obtain ⟨v, hv⟩ := exists_nonzero_boundary K
    rcases roots_classes K g hg v with h | h
    · exact (hv h).elim
    · intro hZero
      exact hv (h.trans hZero)
  let l : ℤ →+ HR K :=
    { toFun := fun n => n • b
      map_zero' := zero_zsmul b
      map_add' := fun m n => add_zsmul b m n }
  have hTwo : l 2 = 0 := by
    change (2 : ℤ) • b = 0
    calc
      (2 : ℤ) • b = b + b := by simpa using two_zsmul b
      _ = boundary K (Additive.ofMul (g ^ (2 : ℕ))) := by
        rw [pow_two]
        exact (map_add (boundary K) (Additive.ofMul g) (Additive.ofMul g)).symm
      _ = 0 := boundary_square_zero K g
  let f := ZMod.lift 2 ⟨l, hTwo⟩
  have hf : f 1 = b := by
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by simp]
    dsimp only [f]
    rw [ZMod.lift_coe]
    exact one_zsmul b
  have hCases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  let e := AddEquiv.ofBijective f ⟨by
    intro x y hxy
    rcases hCases x with rfl | rfl <;> rcases hCases y with rfl | rfl
    · rfl
    · exact False.elim (hb (by simpa only [map_zero, hf] using hxy.symm))
    · exact False.elim (hb (by simpa only [map_zero, hf] using hxy))
    · rfl,
    by
      intro v
      rcases roots_classes K g hg v with h | h
      · exact ⟨0, (map_zero f).trans h.symm⟩
      · exact ⟨1, hf.trans h.symm⟩⟩
  let t : Additive (rootsOfUnity 2 K) ≃+ ZMod 2 :=
    (CuspRootCoefficients.rootsOfUnityEquivZModOfPrimitiveRoot
      (primitiveNegOne K)).toAdditive
  let ti := (constantSheaf (J K) AddCommGrpCat.{0}).mapIso
    (t.toAddCommGrpIso : KummerConstantCoefficients.coefficientGroup K 2 ≅ cyclic)
  exact e.trans (((Sheaf.functorH (J K) 1).mapIso ti).addCommGroupIsoToAddEquiv.trans
    (cohomologyEquiv (R K) cyclic 1))

end

end ManuscriptAudit.ArithmeticFinitePointHOne

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.ArithmeticFinitePointHOne.finitePointCyclicHOneEquiv
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
