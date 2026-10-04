# 순환 후보 191개 — 전체 목록과 분류

## 무엇을 탐지했나

`circularity_lint.py`는 **증명 전체가 "이름 붙은 `Prop` 정의를 타입으로 갖는 가설을 그대로 적용"하는 정리**를 찾습니다. 예: `theorem t (h : P x) : Q := h x`, `:= h.1`, `:= by exact (h x).mp`. 이런 정리는 가설 이상을 증명하지 않습니다.

- 가설이 **실제 정의**라면 분해 보조정리(API)이므로 정상입니다. 예: `IsNthPrime.prime := h.1`.
- 가설이 **논문 주장·게이트·인증서**인데 그 정리를 논문 결과로 내세우면 **순환**입니다.

따라서 191개를 모두 "순환 정리"라고 부르는 것은 과장이며, 아래처럼 분류했습니다. 분류 근거는 68개 가설 정의와 해당 정리를 직접 읽고 판단한 것입니다.

| 분류 | 개수 | 조치 |
|---|---|---|
| **A** 순환·동어반복 (논문 결과로 제시) | 10 | 수정 필수: 해소 증명, 삭제, 또는 정직한 개명 + 원장 수정 |
| **B** 논문 주장/인증서 묶음의 재진술 분해 | 131 | 삭제 또는 API로 격리. 증거로 집계 금지 (Mock1_Advanced 121개) |
| **C** 실제 정의의 API 분해 / 탐지 오탐 | 46 | 유지 (`allowlist.txt`에 등록됨) |
| **D** 조건부이나 같은 파일에서 가설이 증명됨 | 4 | 유지 + 가설 없는 따름정리 추가 |

자동 탐지가 놓치는 순환·공허 항목 62개는 [`SUPPLEMENTARY.md`](SUPPLEMENTARY.md)에 있습니다. 증명이 길거나 TFAE로 조립하는 경우, 필드가 결론인 경우, 만족 불가능한 인터페이스 등입니다. 실제로 수정해야 할 핵심 항목은 **A 10개 + 보충 62개**이고, B 131개는 정리(삭제) 작업입니다.

파일: [`CHECKLIST.md`](CHECKLIST.md) (191개 체크리스트) · [`SUPPLEMENTARY.md`](SUPPLEMENTARY.md) · [`circular_candidates_classified.csv`](circular_candidates_classified.csv) · [`allowlist.txt`](allowlist.txt) · [`CODEX_PROMPT.md`](CODEX_PROMPT.md)

## A. 순환·동어반복 — 수정 필수 (10)

| 가설 정의 | 정리 (모듈:행) | 비고 |
|---|---|---|
| `SatisfiesHasse` (Spt1:2370) | C001 `ec_hasse` (Spt1:2378) | Hasse 한계 자체를 가정해 `ec_hasse`로 제시(독스트링은 조건부임을 명시). 래퍼 정리 삭제 또는 외부 입력으로만 남기고 원장 표기 수정. |
| `GoldwasserKilianPropagationTheorem` (Spt1:3082) | C003 `ECStepCertificate.sound_of_GK` (Spt1:3088) | GK 전파 정리를 가정. 게다가 `ECStepCertificate E X` 필드가 X를 제약하지 않아 진술이 거짓일 가능성(감사 보고 Spt1). 진술을 바로잡거나 삭제. 거짓 가설을 남기지 말 것. |
| `MtALogInput` (Spt1:3912) | C005 `rmk2_2_uniform_remainder` (Spt1:3980) | 정의가 결론 `k ≤ v_p(Λ−u)` 그 자체(Remark 2.2로 표기). 파일의 `padicLog1p` 결과로 해소 시도, 불가하면 래퍼 삭제. |
| `AKSIsComplete` (Spt3:781) | C007 `prime_iff_section_of_complete` (Spt3:785)<br>C009 `theorem18_of_any_complete` (Spt3:6079) | `∀ X, X.Prime ↔ FEC X`를 가정해 `X.Prime ↔ FEC X`를 결론(Theorem 18로 표기). 삭제 또는 `_of_assumed_complete`로 개명하고 인증 목록·경계 레코드에서 제거. |
| `DirichletDensityAP` (Spt4:2274) | C010 `thm836_part2` (Spt4:2280) | 디리클레 밀도 정리를 가정해 `thm836_part2`로 제시(독스트링은 조건부 명시). Mathlib로 해소 가능한지 확인, 불가하면 래퍼 삭제. |
| `goodReduction` (Spt5:506) | C011 `claim91_necessary` (Spt5:2784) | `goodReduction := ¬ p ∣ Δ`의 정의 동어반복을 'Claim 9.1 (necessary)'로 표기. `goodReduction_iff` 같은 정의 API로 개명하고 논문 라벨 제거. |
| `goodOpen` (Spt2:641) | C013 `goodOpen_to_etalePiece` (Spt6:5043) | `etalePiece := goodOpen`으로 정의해 놓고 étale 다리로 제시(정의 동어반복). 프록시 정의 제거 또는 '모델'로 명시. |
| `CoeffAgreement` (Spt6:6031) | C014 `ext_of_coeffAgreement` (Spt6:6036) | `CoeffAgreement p q := p = q`로 '계수 강성'을 제시(동어반복, 원장이 unconditional로 표기). 정의 삭제, 사용처를 `p = q`로 대체, 원장 수정. |
| `ModularCovarianceRestrictionStable` (Mock2:13572) | C156 `modularCovariance_restrict` (Mock2:13584) | 추상 Lemma 6.1을 가정 그 자체로 제시. 기하판 `lemma6_1`(Mock2 17325, 실제 증명)로 대체하거나 삭제. |

## B. 재진술 분해 — 삭제 또는 격리 (131)

| 가설 정의 | 정리 (모듈:행) | 비고 |
|---|---|---|
| `gateECRegularData` (Spt1:2674) | C002 `gateECRegularData_forces_deltaShadow` (Spt1:2706) | 논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것. |
| `gateECRegularModelData` (Spt1:3166) | C004 `gateECRegularModelData_forces_deltaShadow` (Spt1:3178) | 논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것. |
| `WeightPurityGate` (Spt7:11878) | C016 `weightPurityGate_pure` (Spt7:11885)<br>C017 `weightPurityGate_detTraceExpansion` (Spt7:11893) | 논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것. |
| `EquivalenceCGate` (Spt7:11919) | C018 `equivalenceCGate_arithmetic` (Spt7:11926)<br>C019 `equivalenceCGate_weightPurity` (Spt7:11934) | 논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것. |
| `GlobalRiemannHypothesisGate` (Spt7:12501) | C020 `GlobalRiemannHypothesisGate.zeroPoleCircle` (Spt7:12509)<br>C021 `GlobalRiemannHypothesisGate.eulerProduct` (Spt7:12517)<br>C022 `GlobalRiemannHypothesisGate.noCancellation` (Spt7:12525) | 논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것. |
| `PaperInstancesHRlfCoefficientStatement` (Mock1_Advanced:35834) | C034 `coeff_eq_object_at` (Mock1_Advanced:36171)<br>C035 `coefficientAt_eq_object_at` (Mock1_Advanced:36177)<br>C036 `rademacher_decomposition_at` (Mock1_Advanced:36183) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfTailStatement` (Mock1_Advanced:35843) | C037 `t1t5_cutoff_at` (Mock1_Advanced:36194)<br>C038 `analytic_cutoff_at` (Mock1_Advanced:36200) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfLerchPrincipalStatement` (Mock1_Advanced:35849) | C039 `principal_laurent_at` (Mock1_Advanced:36210)<br>C040 `polar_negative_at` (Mock1_Advanced:36218)<br>C041 `order_one_at` (Mock1_Advanced:36224) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfFiniteSolveStatement` (Mock1_Advanced:35858) | C042 `integer_solve_at` (Mock1_Advanced:36233)<br>C043 `rational_solve_at` (Mock1_Advanced:36241)<br>C044 `complex_residual_zero_at` (Mock1_Advanced:36249) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfSPTCRTTorStatement` (Mock1_Advanced:35870) | C045 `equalizer_at` (Mock1_Advanced:36259)<br>C046 `tor_order_gcd_at` (Mock1_Advanced:36267)<br>C047 `crt_pairwise_at` (Mock1_Advanced:36275)<br>C048 `prime_gate_two_at` (Mock1_Advanced:36285)<br>C049 `precision_one_at` (Mock1_Advanced:36290)<br>C050 `obstruction_one_at` (Mock1_Advanced:36295) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfPAdicMahlerStatement` (Mock1_Advanced:35889) | C051 `overlap_mod_m_at` (Mock1_Advanced:36304)<br>C052 `overlap_prime_power_at` (Mock1_Advanced:36311)<br>C053 `mahler_congruence_at` (Mock1_Advanced:36320)<br>C054 `mahler_expansion_at` (Mock1_Advanced:36329)<br>C055 `binomial_congruence_at` (Mock1_Advanced:36338)<br>C056 `binomial_expansion_at` (Mock1_Advanced:36346) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfOlsRowStatement` (Mock1_Advanced:35918) | C057 `prediction_formula_at` (Mock1_Advanced:36359)<br>C058 `residual_decomposition_at` (Mock1_Advanced:36370)<br>C059 `residual_bound_at` (Mock1_Advanced:36378) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfEntropyCardyStatement` (Mock1_Advanced:35932) | C060 `entropy_limit_at` (Mock1_Advanced:36389)<br>C061 `alpha_interval_at` (Mock1_Advanced:36399)<br>C062 `ceff_interval_at` (Mock1_Advanced:36405) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfFinalInstanceStatement` (Mock1_Advanced:35944) | C063 `object_name_at` (Mock1_Advanced:36415)<br>C064 `principal_order_one_at` (Mock1_Advanced:36421)<br>C065 `alpha_interval_at` (Mock1_Advanced:36426)<br>C066 `beta_interval_at` (Mock1_Advanced:36432) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfChannelStatement` (Mock1_Advanced:35953) | C067 `tail_at` (Mock1_Advanced:36442)<br>C068 `lerch_principal_at` (Mock1_Advanced:36447)<br>C069 `finite_solve_at` (Mock1_Advanced:36452)<br>C070 `spt_crt_tor_at` (Mock1_Advanced:36457) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `PaperInstancesHRlfSpineRowStatement` (Mock1_Advanced:35959) | C071 `coefficient_at` (Mock1_Advanced:36474)<br>C072 `padic_mahler_at` (Mock1_Advanced:36480)<br>C073 `ols_row_at` (Mock1_Advanced:36486)<br>C074 `entropy_cardy_at` (Mock1_Advanced:36492)<br>C075 `final_instance_at` (Mock1_Advanced:36498) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIObjectSchemaPromptObjective` (Mock1_Advanced:44914) | C076 `claim_registry_at` (Mock1_Advanced:45249)<br>C077 `coefficient_schema_at` (Mock1_Advanced:45256)<br>C078 `paper_object_data_instance_at` (Mock1_Advanced:45263)<br>C079 `scalar_jacobi_degeneracy_at` (Mock1_Advanced:45279) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIT1T5PromptObjective` (Mock1_Advanced:44935) | C080 `principal_part_rational_solve_at` (Mock1_Advanced:45291)<br>C081 `completion_shadow_holomorphic_at` (Mock1_Advanced:45301)<br>C082 `cusp_transport_at` (Mock1_Advanced:45310)<br>C083 `appell_lerch_block_formula_at` (Mock1_Advanced:45321)<br>C084 `principal_exponent_formula_at` (Mock1_Advanced:45335)<br>C085 `paper_matrix_rhs_solution_at` (Mock1_Advanced:45347)<br>C086 `fixed_shadow_unary_theta_at` (Mock1_Advanced:45357)<br>C087 `inside_outside_qseries_at` (Mock1_Advanced:45368) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIISPTPromptObjective` (Mock1_Advanced:44987) | C088 `nat_gcd_lcm_at` (Mock1_Advanced:45384)<br>C089 `primewise_thickness_at` (Mock1_Advanced:45399)<br>C090 `valuation_certificate_at` (Mock1_Advanced:45409)<br>C091 `obstruction_failure_at` (Mock1_Advanced:45426)<br>C092 `base_change_at` (Mock1_Advanced:45437) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIKernelPromptObjective` (Mock1_Advanced:45031) | C093 `kernel_selection_at` (Mock1_Advanced:45454)<br>C094 `multiplier_phase_at` (Mock1_Advanced:45465)<br>C095 `cusp_convergence_at` (Mock1_Advanced:45476)<br>C096 `transport_family_at` (Mock1_Advanced:45486)<br>C097 `kernel_table_at` (Mock1_Advanced:45497)<br>C098 `multiplier_input_at` (Mock1_Advanced:45509)<br>C099 `cusp_input_at` (Mock1_Advanced:45519)<br>C100 `transport_across_cusps_at` (Mock1_Advanced:45529) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIExactPromptObjective` (Mock1_Advanced:45080) | C101 `coefficient_separation_at` (Mock1_Advanced:45544)<br>C102 `theta_character_at` (Mock1_Advanced:45554)<br>C103 `spectral_kloosterman_at` (Mock1_Advanced:45565)<br>C104 `local_euler_at` (Mock1_Advanced:45577)<br>C105 `root_filter_at` (Mock1_Advanced:45585)<br>C106 `exact_formula_at` (Mock1_Advanced:45593)<br>C107 `paper_formula_fields_at` (Mock1_Advanced:45605) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIPAdicPromptObjective` (Mock1_Advanced:45124) | C108 `normalization_at` (Mock1_Advanced:45624)<br>C109 `overlap_at` (Mock1_Advanced:45636)<br>C110 `mahler_at` (Mock1_Advanced:45647)<br>C111 `tail_zero_at` (Mock1_Advanced:45664)<br>C112 `face_tracking_at` (Mock1_Advanced:45674)<br>C113 `denominator_data_at` (Mock1_Advanced:45689)<br>C114 `chart_vectors_at` (Mock1_Advanced:45699)<br>C115 `mahler_table_at` (Mock1_Advanced:45708)<br>C116 `analytic_range_predicate_at` (Mock1_Advanced:45725)<br>C117 `obstruction_failure_at` (Mock1_Advanced:45734) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIEntropyPromptObjective` (Mock1_Advanced:45196) | C118 `regression_cardy_at` (Mock1_Advanced:45747)<br>C119 `rademacher_tail_at` (Mock1_Advanced:45757)<br>C120 `entropy_cardy_wrapper_at` (Mock1_Advanced:45768)<br>C121 `alpha_extraction_at` (Mock1_Advanced:45780)<br>C122 `degeneracy_at` (Mock1_Advanced:45788)<br>C123 `ols_interval_at` (Mock1_Advanced:45797)<br>C124 `growth_stability_at` (Mock1_Advanced:45809)<br>C125 `reproducibility_schema_at` (Mock1_Advanced:45821)<br>C126 `external_rows_at` (Mock1_Advanced:45832) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIRlfCoefficientMathStatement` (Mock1_Advanced:60018) | C127 `coeff_eq_object_at` (Mock1_Advanced:60099)<br>C128 `coefficientAt_eq_object_at` (Mock1_Advanced:60105)<br>C129 `rademacher_decomposition_at` (Mock1_Advanced:60111) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIRlfFiniteArithmeticStatement` (Mock1_Advanced:60027) | C130 `tail_at` (Mock1_Advanced:60133)<br>C131 `lerch_principal_at` (Mock1_Advanced:60138)<br>C132 `finite_solve_at` (Mock1_Advanced:60143)<br>C133 `spt_crt_tor_at` (Mock1_Advanced:60148)<br>C134 `channel_statement_at` (Mock1_Advanced:60153) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIRlfPAdicMahlerMathStatement` (Mock1_Advanced:60033) | C135 `overlap_mod_m_at` (Mock1_Advanced:60162)<br>C136 `overlap_prime_power_at` (Mock1_Advanced:60169)<br>C137 `overlap_pair_at` (Mock1_Advanced:60178)<br>C138 `mahler_congruence_at` (Mock1_Advanced:60190)<br>C139 `mahler_expansion_at` (Mock1_Advanced:60199)<br>C140 `binomial_congruence_at` (Mock1_Advanced:60222)<br>C141 `binomial_expansion_at` (Mock1_Advanced:60230) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIRlfEntropyRegressionMathStatement` (Mock1_Advanced:60062) | C142 `entropy_limit_at` (Mock1_Advanced:60256)<br>C143 `ols_row_at` (Mock1_Advanced:60266)<br>C144 `ols_prediction_formula_at` (Mock1_Advanced:60282)<br>C145 `ols_residual_decomposition_at` (Mock1_Advanced:60293)<br>C146 `ols_residual_bound_at` (Mock1_Advanced:60301)<br>C147 `alpha_interval_at` (Mock1_Advanced:60308)<br>C148 `ceff_interval_at` (Mock1_Advanced:60314) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `AdvancedClaimsIIRlfFinalMathStatement` (Mock1_Advanced:60086) | C149 `final_detail_at` (Mock1_Advanced:60324)<br>C150 `final_instance_at` (Mock1_Advanced:60329)<br>C151 `object_name_at` (Mock1_Advanced:60334)<br>C152 `principal_order_one_at` (Mock1_Advanced:60340)<br>C153 `alpha_interval_at` (Mock1_Advanced:60345)<br>C154 `beta_interval_at` (Mock1_Advanced:60351) | 퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장. |
| `UniformError` (QYM:5780) | C173 `individual_eigenvalue_error` (QYM:5791) | 가설 `UniformError`가 논문 Thm 4.31의 결론(정직하게 가설로 표기). 분해 정리 자체는 무해하나 이를 소비하는 정리가 '증명'으로 집계되지 않게 할 것. |

## D. 조건부이나 같은 파일에서 해소됨 — 유지 + 무조건 따름정리 (4)

| 가설 정의 | 정리 (모듈:행) | 비고 |
|---|---|---|
| `FiniteMahlerBinomialInversion` (Mock1:4766) | C027 `finiteMahlerEval_finiteDifferenceCoeff_eq_of_binomial_inversion` (Mock1:4770) | Mock1 4826에서 해소됨. 가설 없는 무조건 따름정리 추가 권장. |
| `FiniteMahlerInterpolationUnique` (Mock1:4778) | C028 `finiteMahler_coefficients_unique` (Mock1:4783)<br>C029 `finiteMahler_interpolating_coeffs_eq_finiteDifferenceCoeff` (Mock1:4791) | Mock1 4853에서 해소됨. 가설 없는 무조건 따름정리 추가 권장. |
| `GammaTwoThreeCuspCompactCofinal` (Mock2_FunctionalAnalysis:10545) | C165 `SmoothCompactCore.exists_quotientSupport_subset_threeCuspTruncation_of_compactCofinal` (Mock2_FunctionalAnalysis:11493) | Mock2_FA 10532/10710에서 해소됨(`gammaTwoGeometricCompactCofinal_unconditional`). 무조건 따름정리 추가 권장. |

## C. 정상 API 분해 / 탐지 오탐 — 유지 (46)

| 가설 정의 | 정리 (모듈:행) | 비고 |
|---|---|---|
| `Hk` (Spt1:460) | C006 `Hk_phiTerm_bound` (Spt1:3990) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `FnumWindow` (Spt3:4918) | C008 `FnumWindow_imp_Fnum_layer` (Spt3:4926) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IsGammaAcyclic` (Spt6:771) | C012 `IsGammaAcyclic.h1_subsingleton` (Spt6:778) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `HasWeakRegularSequenceLength` (Spt7:6681) | C015 `exists_weaklyRegular_of_hasWeakRegularSequenceLength` (Spt7:6699) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IsNthPrime` (Spt7:15115) | C023 `prime` (Spt7:15120)<br>C024 `card_primes_lt` (Spt7:15123) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `PIntegralOn` (Mock1:3898) | C025 `PIntegralOn.denominator_coprime` (Mock1:3901) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `FiniteMahlerInterpolates` (Mock1:4730) | C026 `FiniteMahlerInterpolates.apply` (Mock1:4734) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IntegerGlobalLiftModLcm` (Mock1:5773) | C030 `integerGlobalLiftModLcm_apply` (Mock1:5777) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `HasFiniteWeightSupport` (Mock1:6043) | C031 `finiteWeightSupport_apply` (Mock1:6046) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `Mem` (Mock1:6406) | C032 `lower_le_of_mem` (Mock1:6409)<br>C033 `le_upper_of_mem` (Mock1:6413) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `FlatSector` (Mock2:13916) | C155 `curvature_eq_zero` (Mock2:9085) | 정의가 `QCurvature x = x`로 되어 있어 의도(=0?) 확인 필요. |
| `GaugeCovariant` (Mock2:13905) | C157 `gauge_covariance_formula` (Mock2:13909) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `MassConditionAt` (Mock2_Advanced:1520) | C158 `MassConditionAt.mass_pos` (Mock2_Advanced:1563) | 한 단계 `trans_le` 유도(정상). |
| `ComplexCoerciveWith` (Mock2_FunctionalAnalysis:1528) | C159 `alpha_pos` (Mock2_FunctionalAnalysis:1537)<br>C160 `diagonal` (Mock2_FunctionalAnalysis:1540) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `RealSmooth` (Mock2_FunctionalAnalysis:10972) | C161 `measurable` (Mock2_FunctionalAnalysis:11014) | 실제 보조정리를 쓰는 짧은 증명(탐지 오탐). |
| `HasQuotientCompactSupport` (Mock2_FunctionalAnalysis:11026) | C162 `add` (Mock2_FunctionalAnalysis:11066)<br>C163 `smul` (Mock2_FunctionalAnalysis:11073)<br>C164 `mul_right` (Mock2_FunctionalAnalysis:11081)<br>C166 `HasQuotientCompactSupport.raiseRaw` (Mock2_FunctionalAnalysis:12973)<br>C167 `HasQuotientCompactSupport.lowerRaw` (Mock2_FunctionalAnalysis:12979)<br>C168 `HasQuotientCompactSupport.laplaceRaw` (Mock2_FunctionalAnalysis:12985) | 실제 보조정리를 쓰는 짧은 증명(탐지 오탐). |
| `IsPlanarAffineWeakGraph` (Mock2_FunctionalAnalysis:44319) | C169 `IsPlanarAffineWeakGraph.friedrichs_raising_identity` (Mock2_FunctionalAnalysis:46204)<br>C170 `IsPlanarAffineWeakGraph.friedrichs_loweringFromSucc_identity` (Mock2_FunctionalAnalysis:46218) | 보조정리 `friedrichs_identity` 경유(탐지 오탐). |
| `IsScalarQCyclic` (QYM:665) | C171 `upperHalfPlaneQ_trace_eq_zero` (QYM:692) | 보조정리 `eq_zero_of_ne_one` 경유(탐지 오탐). |
| `IsWeakCriticalAt` (QYM:5054) | C172 `IsWeakCriticalAt.firstVariation_eq_zero` (QYM:5072) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `FormSmall` (QYM:6312) | C174 `formSmall_relativeCoefficient_nonneg` (QYM:6365)<br>C175 `formSmall_relativeCoefficient_lt_one` (QYM:6371)<br>C176 `formSmall_remainderCoefficient_nonneg` (QYM:6377)<br>C177 `formSmall_relativeBound` (QYM:6383) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `HasRootExponentialBound` (QYM:11709) | C178 `abs_le_rootExponentialEnvelope` (QYM:11725) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IsAdmissibleVariation` (QYM:12346) | C179 `admissibleVariation_base` (QYM:12356)<br>C180 `admissibleVariation_tangent` (QYM:12367)<br>C181 `admissibleVariation_update` (QYM:12378) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `CoerciveOn` (QYM:12534) | C182 `coerciveOn_constant_pos` (QYM:12541)<br>C183 `coerciveOn_bound` (QYM:12548) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `HasComplexRootExponentialBound` (QYM:15288) | C184 `coefficient_norm_le_of_complexRootExponentialBound` (QYM:15303) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IsPositiveCoerciveShift` (QYM:20761) | C185 `IsPositiveCoerciveShift.shift_pos` (QYM:20766)<br>C186 `IsPositiveCoerciveShift.coercivityConstant_pos` (QYM:20772)<br>C187 `IsPositiveCoerciveShift.shift_pos` (QYM:23293)<br>C188 `IsPositiveCoerciveShift.constant_pos` (QYM:23299) | 20766/23293에 같은 이름 분해 정리 중복 — 하나로 합칠 것. |
| `IsGaugeDeckPullbackRepresentation` (QYM:30893) | C189 `IsGaugeDeckPullbackRepresentation.one` (QYM:30902)<br>C190 `IsGaugeDeckPullbackRepresentation.mul` (QYM:30911) | 실제 정의의 표준 분해(API) 보조정리. 유지. |
| `IsSquareIntegrableOnActualStage` (QYM:50917) | C191 `quotientSectionToActualStageL2_coeFn_ae` (QYM:50947) | Mathlib `coeFn_toLp` 경유(탐지 오탐). |
