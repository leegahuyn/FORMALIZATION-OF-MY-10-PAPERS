# (WORKING NOTES — to be replaced by final report)
## 1-1150
- Header 84-118: paper "Global Poincare Matching and Kloosterman-Compatible Test Kernels for Half-Integral Weight Mock-Theta Gauge Objects", corrections to Defs 1-18. Claims "independently constructs genuine metaplectic cover and standard unary-theta multiplier from two explicit parabolic lifts, central lift, Gamma(2) generation theorem, two-sheet fiber classification".
- Gamma2 = CongruenceSubgroup.Gamma 2 (faithful); hyperbolicMeasure = Mathlib volume; gamma2Act_measurePreserving (160) genuine via measurePreserving_smul.
- ConcreteUnaryTheta (212-410): theta = jacobiTheta; norm_theta_le_one_add_inv_sqrt_im (372) genuine sum-integral comparison + integral_gaussian_Ioi. (U) good.
- ConcreteMellinGamma.integral_beta_sub_two (436) Mathlib wrapper.
- Gamma2Metaplectic (450): matrix + arbitrary unit-valued function; Group via ofLeftAxioms (507). NOTE: this is semidirect product Γ(2) ⋉ (H→ℂˣ), not the double cover.
- HalfWeightAutomorphyFactor (545) cocycle structure; FixedGamma2MetaplecticLift.trivial (574) factor=1 degenerate, labelled "normalization check only".
- WeightedSobolevDatum (670): abstract H, norm_sq_eq_energy field, closedness field; Def1 = topologicalClosure. Riesz wrappers (867-1000).
- Gamma2Cusp 3 labels (1006), width const 2, strictWidth_scaling_conjugate_eq_width (1064) genuine bridge to Mathlib strictWidthInfty.
- cuspHeight_zero/one (1105/1115) genuine; pairwise_disjoint_strictCuspHoroball (1216) genuine nlinarith.
## 1150-2250
- cuspQCoordinate_eq_qParam (1242) bridge. truncation lemmas; IsCompact.exists_truncationHeight (1350) genuine easy.
- TruncationCertificate (1375) Prop structure: compact field remains assumption.
- ContinuousSpectralData (1395) abstract; massFunctional; HMass (1525) predicate; continuousMassAtCusp_pos_iff_activity (1462) Mathlib wrapper.
- RankinSelbergData (1669) abstract measure/kernel/eisenstein (no real Eisenstein series). hermitianContraction_invariant (1637) genuine small.
- CuspQChart (1726): homeomorphism given as data; lpPushLinearIsometryEquiv (1903) genuine construction.
- QLocalSystem (1952): trivialization is data; all transport theorems trivial consequences. QLocalSystem.constant degenerate example labelled.
- ConvergentQSeries (2165), InsideOutsideMatch (2200): continuation_formula field; inside_dictionary etc. accessor-chains.
## 2250-3350
- LinearPresheaf (2269): ad-hoc presheaf (sections as submodules of one ambient module), NOT Mathlib's CategoryTheory sheaf; IsLinearSheaf (2282) locality+gluing Prop. No bridge to Mathlib TopCat.Sheaf.
- QGaugeVariableSheaf (2399): sheafification universal property stored as data fields; factor_existsUnique (2427) accessor repackaging.
- RadialDerivation (2480), AlgebraicRadialConnection (2501), AlgebraicTensorRadialConnection (2532): interfaces; pure_tensor_rule is a field.
- balanced equalizer (2571-2891): balancedPresheaf_isSheaf (2882) genuine (equalizer of sheaf morphisms is sheaf) — real but elementary.
- GaugeDescentAction (2906) abstract; GaugeDescentSheaf.covariant_gluing (3039) genuine elementary.
- TrivialBundleSectionSheaf.isLinearSheaf (3259) genuine concrete instance (zero-extended set-theoretic functions); trivialAction = identity (degenerate).
## 3350-4450
- TrivialBundleSectionSheaf.gaugeSheaf (3357) trivial action; concrete_covariant_gluing_existsUnique (3374) specialization.
- CurvatureCalculus (3406): d, wedge arbitrary linear maps — no exterior derivative; curvature = bg + dA + A∧A; expansions simp. EffectiveActionDecomposition (3560) decomposition is a field; minimizer theorems linarith (T-ish).
- Elementary (3724), FunctionalAnalysis (3759): Mathlib wrappers (lax_milgram 3771 = IsCoercive.continuousLinearEquivOfBilin).
- ConditionalSkeleton.spectral_mass_gap (3785): `0<ε → 1/4+ε ≤ λ0 → 1/4 < λ0` linarith — trivial but honestly documented.
- CorrectedLemmas.GenuineGamma2Metaplectic.Element (3876): sqrtFactor^2 = denom, continuous — GENUINE double-cover ambient. Group (4032). two-sheet: sqrtFactor_eq_or_eq_neg_of_matrix_eq (4099) via clopen/connectedness; eq_or_eq_deckNeg_mul_of_projection_eq (4201) (U). deckNeg central, nontrivial.
- ThetaGeneratorLift: translationTwoLift (4235) over T^2; theta_translationTwoLift_covariance (4274) (U, wrapper). centralNegOneLift (4307). no_groupHom_section_of_genuine_projection (4387) (U) genuine non-splitting — correct.
- GenuineHalfWeightDensity (4403): density sqrt(y)|u|^2; im_mul_norm_pow_four_invariant (4433) genuine.
## 4450-5550
- density_invariant (4455) genuine. GenuineHalfWeightAutomorphy (4476): Multiplier = Element →* Circle; factor = ν a * sqrtFactor; factor_mul genuine.
- centralNegOne_multiplier_value_of_nonzero (4689), isAutomorphic_one_iff_eq_zero (4752): genuine small obstruction theorems.
- IsThetaCovariant (4802), thetaCovariantSubgroup (4898), theta_nonzero_at_thetaNonzeroPoint (5033) genuine (uses norm_jacobiTheta_sub_one_le at y=log4/π). thetaCovariantProjection_injective (5056) genuine.
- FullThetaCovariance (5082) Prop — DISCHARGED at 21156 `fullThetaCovariance` (verify). thetaMultiplier (5187) built from it, character law derived not postulated.
- GenuineInverseHalfWeightAutomorphy (5248): literal PDF convention (cτ+d)^{-1/2}; density y^{-1/2}|u|^2 invariance genuine (5345); sqrtFactor_norm_inv_eq_one_of_plainNormInvariant (5369) shows PDF's unweighted |u|^2 density wrong — paper-error detection.
- GenuineWeightedSobolev.Datum (5425): same abstract interface as WeightedSobolevDatum, ae_equivariant_closed field.
## 5550-6650
- StartingIntegralIdentity (Lemma 1.1): restrict_dual_equation (5652) = congrArg (T); RegularDensityData (5691) laplace_eq_integral fields; restrict_distributional_equation_compactSupport_of_product (5800) bookkeeping.
- GlobalPoincare (Lemmas 1.2/2.1): unqualifiedPoincareSchema_false (5854) trivial. NonnegativeSelfAdjointData (5863, uses Mathlib LinearPMap IsSelfAdjoint), SpectralMeasureData (5874: measure/mass_eq_norm_sq/energy_eq_operator fields), SpectralGapData (5895: gap + ae lower bound field), HalfWeightAutomorphicLaplacianData (5934) / Genuine... (5988) huge interfaces with normalizedAdmissibleMode anti-vacuity field (good).
- spectral_gap_bound (6149) small genuine integral_mono_ae; globalPoincare_sq (6204), genuineHalfWeightAutomorphic_globalPoincare_sq (6223), halfWeightAutomorphic_globalPoincare_sobolevEnergy_sq_of_orthogonal (6327): (C) — hypothesis = spectral gap ≥ gap on admissible + energy identity field → Poincare. Near-tautological (gap IS the Poincare content) but honestly stated.
- KloostermanTail (Lemma 1.3/2.2): finite_summation_by_parts (6402) genuine induction; AbelCancellationCertificate (6426) fields; hasOrderedSum (6455) genuine; not_summable_paper_tail_one/half (6484/6492) genuine paper-error detection (c^{-1+ε} tail diverges). orderedKernel_and_bound (6550) (C).
- CuspConvergence (6608, Lemmas 3.1-3.4): exponent arithmetic linarith.
## 6650-7750
- CuspConvergence: cuspPowerDensity_integrable_iff (6661) wrapper integrableOn_Ioi_rpow_iff; cuspPowerDensity_integral_strip (6720) Fubini; AllCuspPowerEstimate (6759)/CuspIndexedPowerEstimate (6839) structures with norm_le field; integrableAtEveryCusp (C, dominated). 
- PAPER-ERROR DETECTIONS (U): not_CitedLemma31RankinSelbergInference (7060) (bare window ⇏ Rankin-Selberg integrability, α=-1,σ=2); nearZero_beta_one_not_integrable (7098) (Mock-I near-zero range reversed); citedMockOneNormalization_tendsto_zero (7141) (1/Γ(ε)→0 so claimed nonzero normalization is 0). 
- GlobalCuspDecomposition (7170) covers field — assembly.
- TentKernel (Lemma 3.2/3.3): box_convolution_eq_profile (7268) genuine convolution; integral_profile (7378) = T²; setIntegral_profile_abs_ge (7466); integral_cexp_mul_profile (7589) IBP; fourier_profile_eq_cosine_of_ne_zero (7721) genuine Fejér-kernel Fourier transform via Mathlib 𝓕. Real math.
## 7750-8850
- fourier_profile_eq_fourierProfile (7824) squared-sinc; lemma32_correctedAndProved (7854) (U), lemma33_correctedAndProved (7868) (U) aggregates — genuine.
- KuznetsovInterface: Convention (7897) abstract measure/normalization/kernel + nontriviality field; TentCertificate (7981) kernel bound field → TentCertificate.bound (8000) (C) genuine estimate.
- smoothTentBump via Mathlib ContDiffBump (8078); bumpSmoothTentMember (8183) concrete.
- smoothTentAutocorrelationRaw (8271) b⋆b; fourier_smoothTentAutocorrelationRaw_eq_normSq (8378) genuine convolution theorem (Real.fourier_mul_convolution_eq) + fourier_conjneg (8203). lemma34_smoothReplacement_correctedAndProved (8610) (U) — explicitly a *replacement* test, not paper kernel.
- profileBesselConvention (8728): toy kernel tent×envelope, labelled "verification model, not the paper's Kuznetsov kernel" (degenerate-but-honest reference instance). normalization_choice_changes_transform (8772) trivial.
## 8850-9950
- UniformKernelEnvelope.smoothTent_bound (8857) (C on kernel envelope) genuine dominated estimate; profileBesselConvention_sameTestCertificate (8955) concrete only for toy kernel.
- KuznetsovKloosterman: UnitNormResidueWeight (9009) arbitrary unit weights; halfIntegralPhase via ZMod.stdAddChar (9045) faithful; halfIntegralUnitResidueSum (9098) NOT the Γ(2) Kloosterman sum (says so).
- gamma2CuspBoundaryPoint (9119) on OnePoint ℝ, injective (9160); gamma2CuspStabilizer (9166) real stabilizer; natAbs_scaledLowerLeft_eq_of_doubleCoset (9309) genuine (modulus |c| descends to double coset) — real math.
- Gamma2CuspPairKernel (9344): representativeTerm abstract; constantUnitGamma2CuspPairKernel (9379) term=1, labelled not paper kernel (degenerate but honest). Gamma2CuspPairFiniteData finiteness field.
- CancellationData (9532): weil_bound + AbelCancellationCertificate + tail_bound fields (the entire Kuznetsov cancellation is assumed) → orderedKloosterman_and_bound (9563) (C) ~ accessor of Abel theorem. pairGcd_unbounded trivial.
- ConcreteTwistedKloosterman (9711): faithful finite twisted Kloosterman sum with Circle multiplier; norm_twistedKloostermanSum_le_card (9825) trivial bound; cancellingMultiplierPhase (9868) shows trivial bound sharp for arbitrary multipliers (honest). No Weil bound proved.
- MassUnfolding (9900, Lemmas 3.5-3.8): MeasurableExhaustion; tendsto_setIntegral (9910) Mathlib wrapper; ProperMeasurableExhaustion anti-degeneracy fields.
## 9950-11050
- MassUnfolding truncation monotonicity/limits (9969-10054) genuine small (setIntegral_mono_set, tendsto_finset_sum).
- not_all_re_gt_one_resolvents_poleFree (10106) PAPER-ERROR detection (s=2 real pole of s(1-s)+t²); RankinSelbergPoleFreeParameter, concrete s=2+i (10174) genuine.
- RankinSelbergMassFamily (10204): massExtraction / massTestExtraction arbitrary functions, rankinSelbergIntegrand abstract — no real Eisenstein/Rankin–Selberg object.
- RankinSelbergSpectralFormulaAtParameter (10266): `formula` field = paper's (3.2) identity assumed; rankinSelbergObject_eq (10304) (A) accessor.
- RankinSelbergToMassCertificate (10337): extracted_mass_eq field — near-CIRCULAR (field is exactly the mass identification). 
- FiniteTruncatedUnfolding (10439)/ProductFiniteTruncatedUnfolding (10521): pointwise_decomposition, spectral_identification, geometric_identification fields carry all content; finiteIdentity (10470/10559) genuine assembly (integral_finset_sum, integral_integral_swap). unfolding_to_mass (10619) "Corrected Lemma 3.5" (C) — limit bridge genuine but per-stage identity is assumed.
- Interchange (Lemma 3.6): Mathlib wrappers (integral_tsum_of_summable_integral_norm). constant_arithmetic_series_not_summable (10747) trivial. UniformMajorant, LinkedProductKernelMajorant (10813). ConcreteGeometricMajorant (10879) toy: Dirac measure + (1/2)^i kernel (labelled independent of paper).
- UniformActivity: eventual_spectralActivity (10945), not_hMass_of_tendsto_mass_zero (10958) genuine small; normalized_right_tail_profile_average (10974). Data/LebesgueData (10985/11010) lowerActivity floor fields.
## 11050-12150
- ActiveSetData (11050) → lower_rawActivity (11071) genuine; LebesgueData.toSpectralData (11190); massConditionAt (11325) "Corrected Lemma 3.8" (C): uniform window-activity floor field (substantive deep input: uniform lower bound on Eisenstein coefficients) → HMass. hMass_ofActiveSet (11389).
- RestrictionStability (Lemma 6.1, 11414-11773): restriction preserves pointwise equivariance — trivial (T) but correct.
- CorrectedPropositions (11785): DualNorm (Prop 1) Mathlib wrappers (sSup_unitClosedBall_eq_norm); setIntegral_eq_compactCoreTruncation (11890) small genuine.
- SpectralMassGap errata: no_real_spectralParameter_below_quarter (11934), poincare_does_not_force_coefficient_activity (11942) countermodel, fixedLower_polynomialUpper_consistent (11952), rpow_eventually_dominates (11969) small genuine.
- PositiveMassCriterion.unitCoefficientDiracData (12002): DEGENERATE reference instance (Dirac δ_0 spectral measure, all coefficients ≡1, tent test) ⇒ hMass_unitCoefficientDiracData (12024). Also unitCoefficientFourierPositiveDiracData (12033). Shows interface is satisfiable only by toy data; not real Eisenstein coefficients. zeroCoefficient counterexample (12107). constantUnitary_logDerivative_zero (12117) erratum.
- CommonTestFamily.not_differentiableAt_profile_zero (12130) genuine erratum (raw tent not smooth).
## 12150-13250
- Section54CorollaryRepair: corollary31_eventualContinuousMassLower (12200) = unpack HMass (A/T) — honest docstring: PDF's "nonconditional mass gap" corollaries just restate the hypothesis.
- KuznetsovSpectralIdentity (12266): continuous_identification, spectral/geometric decomposition, trace_identity ALL fields (Kuznetsov formula assumed). DiscreteSpectralSeries (12287) with summability; term_le_contribution (12408) genuine small (tsum_eq_add_tsum_ite).
- corollary33_insertionIntoNormalizedSpectralSum (12561) "Corrected Corollary 3.3" (C) — conclusions are projections of fields + linarith (A-ish).
- AnalyticP2P7Completion: eventual_power_bounds_incompatible (12668) genuine small; spectralGap_of_powerSeparation (12704) / spectralGap_aboveQuarter_of_powerSeparation (12733) (C) — hypothesis hbad_implies_growth ("λ < 1/4+ε ⇒ coefficient growth") is the entire deep content of a mass-gap argument; conclusion follows by contradiction. Not circular strictly but hypothesis ≈ contrapositive of conclusion + geometric bound. SUBSTANTIVE-but-near-circular.
- proposition2_threeInputSkeleton_countermodel (12758): honest — paper's three inputs don't imply Prop 2 (uses Dirac toy data).
- smoothVolumeUnitData (12793): DEGENERATE reference — Lebesgue spectral measure, coefficient ≡ 1 (independent of m!), so mass is m-independent constant; massConditionAt_smoothVolumeUnitData (12928) labelled "Concrete Propositions 3, 4, 6, and 7" — MISLEADING label: the mass condition is trivially satisfied because coefficients don't depend on m; says nothing about Eisenstein coefficients. propositions3to7_sameSmoothTest_completeCertificate (12962) aggregates.
- Corollary33VerificationModel (13008): geometricSide := spectralSide literally, trace_identity := rfl, off-diagonal := continuous mass; corollary33_conclusion (13137) "Closed corrected Corollary 3.3" — TAUTOLOGICAL model (honestly labelled "verification model", not paper's formula).
- LowerGrowth (Props 8-14): exists_pointwise_of_meanSquareBlock (13175), exists_injective_pointwiseMeanSquareSelection (13199) genuine small combinatorics.
## 13250-14350
- LowerGrowth: exists_injective_powerLowerSelection_withAsymptotics (13371) "Full repaired Proposition 8" — genuine elementary combinatorics/asymptotics (IsTheta), given hmean hypothesis. pointwiseLowerGrowth (13417) linear arithmetic.
- StepThree.noTraceComparison_of_infinite_powerGap (13485) genuine small (C: trace equality, upper, lower all hypotheses).
- JacobiDictionary: tautologicalDictionary (13529) honest erratum; SplitProjection (13540) idempotent projection algebra, trivial.
- RademacherControl: not_CitedDampingInequality (13660) PAPER-ERROR (√n ≤ n/√N false); correctedDampingInequality (13674); rademacherSeries_converges_in_H1_and_isAEAutomorphic (13760) (C: summable majorant + terms in core; abstract H); strongCompactness_of_compactEmbedding (13782) Mathlib wrapper; separatedSequence_not_relativelyCompact (13812) genuine small.
- FixedCuspHeightRademacher: sqrtGrowth_le_halfLinear_add_constant (13851) Young; summable_pow_mul_exp_sqrtGrowth_sub_linear (13910) genuine (U), uses Real.summable_pow_mul_exp_neg_nat_mul.
- AnalyticContinuation: isPreconnected_openComplexAnnulus (13989) genuine; analyticOn_eqOn_openComplexAnnulus_of_accumulation (14022) identity theorem on annulus (U) — good real use of Mathlib analytic isolated zeros.
- GlobalUnitCircleMatching (Thm 5.1): S⋆ cancellation (14137) trivial; insideDictionaryCompatibility (14161) shows printed theorem needs missing hypothesis f=2Ψ−S (honest erratum); dictionaryRelation_does_not_force_insideCompatibility (14197) countermodel; no_upperHalfPlane_exterior_q_region (14222) genuine erratum (|q|>1 region in same chart impossible); holomorphic_boundedAlongRadialSegments_not_force_zero (14235) erratum; core_eqOn_annulus_of_completed_sample (14305) genuine identity-theorem application (C on analyticity).
## 14350-15450
- correctedTheorem5_1_annularMatching (14384) "Corrected Theorem 5.1" (C on analyticity + sample agreement) — genuine identity-theorem argument; HalfTwoVerificationModel (14449) toy instance (q⁻¹, w, Ψ=S=q⁻¹, Sstar=q²) honestly labelled not the mock-theta datum; certificate (14671).
- CuspTransport: gamma2_topLeft_ne_zero (14694), not_CitedCuspClaim (14725) PAPER-ERROR genuine (no Γ(2) element sends ∞ to 0 — cusps inequivalent); ambientScalingMatrix_transportCertificate (14746).
- FlatQTransport: connectionOfTrivialization (14783), connectionOfTrivialization_unique (14883) "Corrected Prop 14" — uniqueness given chosen trivialization (T-ish); zeroRadialConnection_ne_identityRadialConnection (14926) non-uniqueness erratum.
- SheafBridge.noUniversalObjectMap (14975) trivial filler.
- OperatorGaugeCurvature: connectionCurvature_variableGauge (15093) "Corrected Prop 17" — (d+A)² conjugation, algebraic (U, trivial); exists_nonzero_gaugeDerivativeTerm (15122).
- FlatMinimizer (15143) linarith. GlobalEqualizer: globalGaugeFormsEquivCompatibleGaugeFamily (15320) "Corrected Prop 20" genuine small (sheaf gluing ⇒ bijection).
- CRTTorBridge (15356, Prop 21): ActualCyclicTorOne uses Mathlib CategoryTheory.Tor (faithful!); comparisonMap_ker (15386), lcmMultiplicationMap_comparisonMap_exact (15419) genuine elementary CRT exactness.
## 15450-16550
- CRTTorBridge cont.: comparisonMap_crtObstructionMap_exact (15493) genuine Bézout; cyclicProjectiveResolution (15756) genuine ProjectiveResolution of ZMod N; actualCyclicTorOneIsoTensorHomology (15782) via isoLeftDerivedObj; actualCyclicTorOneIsoGcd (16097): **Mathlib CategoryTheory.Tor₁(ZMod M, ZMod N) ≅ ZMod (gcd M N) for M,N≠0** — GENUINE, faithful (U) (contrast with Spt-style "Tor := ZMod gcd" proxies). Classical.choice at 16091 only extracts an iso from a constructively-proved Nonempty (harmless). primePowerActualCyclicTorOneIsoGcd (16141). noCyclicTorOneModelEquiv_zeroModulus (16003) correct degeneracy. Upstreamable.
- ConcreteSmoothVolumeUnfolding (16174): rankinSelbergFamily (16284) toy: integrand := 3·smoothTest, coefficients ≡1, Lebesgue; finiteUnfolding_to_mass (16385), productUnfolding_to_mass (16459), extractedMass_pos (16475) — DEGENERATE instance of Lemma 3.5/3.7 interfaces (both sides reduce to same integral by construction). Honestly described as "non-atomic concrete model", but not paper's Rankin–Selberg.
- GreenIdentityRepair (16498): ordered-field arithmetic (T).
## 16550-17700
- WeakVariationalRepair (16577), MockConnectionErratum (16635): scalar linarith errata (T).
- WidthTwoFourier (16674): integral_mode (16682) orthogonality, integral_norm_sq_finitePolynomial (16920) finite Parseval on width-2 horocycle — genuine (U), modest.
- generalizedCRT_exactPackage (16938) aggregate.
- ConcreteGraphCompletion (16959): graphMap into WithLp 2 product; graphMap_norm_sq (17026) — graph-norm identity now a THEOREM (fixes WeightedSobolevDatum's stored norm_sq_eq_energy field). Good repair.
- ClosableGraphBridge (17126): graphCompletion_eq_transportedClosureGraph (17253), graphCompletion_vertical_eq_zero (17397), graphCompletionEquivClosureDomain (17373), isClosable_of_formalAdjoint_dense (17642) — genuine functional analysis using Mathlib LinearPMap (closure, adjoint) (U). FormalAdjointCertificate (17654): integrationByParts field (Maass IBP) remains assumption — SUBSTANTIVE.
## 17700-18850
- MaassJetAudit (17690): two-jet algebra; paper_left/right_factorization_fails_at_height (17748/17757), unweighted_adjoint_claim_fails_at_constant (17775) — PAPER-ERROR detections (Maass Laplacian missing drift term) via jets (finite algebra, genuine but elementary); formalAdjointUnitaryRaise_eq_negUnitaryLower (17841).
- PointwiseMaass (17859): Maass raising/lowering via Mathlib fderiv ℝ on localExtension (faithful definitions); only trivial lemmas.
- HalfOrderBessel (17998): I_{1/2}(x)=√(2/πx) sinh x closed form (faithful special case, no general Bessel bridge); not_summable_criticalModulusEnvelope (18052); no_uniformConstant_absorbs_quarterPower (18069) erratum.
- ConcreteRademacherTruncation (18097): finite truncation of Rademacher-type sum with actual twisted Kloosterman sums × I_{1/2} weight; only trivial card bounds; criticalPointwiseControl_does_not_imply_summable (18363) erratum. No convergence/Weil bound proved.
- HalfOrderWhittaker (18381): W_{0,1/2}=exp(-x/2), ODE (18454), integrals — genuine but elementary.
- CuspQStabilizer (18566): translationMatrix_mem_gamma2 via normality; cuspQCoordinate_translationElement (18636) genuine q-invariance.
- Gamma2SixCellPolygon (18664-): six coset reps of Γ(2) in SL2(Z); reducedRep_bijective (18765) by `decide` on SL2(F2) (small finite decide, fine); exists_rep_mul_gamma2 (18813) genuine; closedCell via Mathlib ModularGroup.fd.
