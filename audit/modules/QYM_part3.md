# QYM part 3 (lines 31401–47000) — 진행 노트 (중간 저장)

## 진행 메모 (Read 31401–37095)
- 31401-31489 P1MatterGaugeDirichletFirewallExtension 끝: DirichletCore = supplied interior core의 topologicalClosure로 *정의* → density는 정의에서 나옴(정직히 명시). dirichletCore_le_traceKernel는 hTraceZero 가정(C).
- 31519-31570 IsLowerSemiboundedOn; 비음 energy ⇒ lower semibounded (T, 0 하한).
- 31574-31739 GaugeBoundary: relative/absolute trace kernels; inducedGaugeParameterBoundaryTraces = field trace ∘ gaugeAction 으로 정의 → compatibility가 "정리"(사실상 정의적 T). canonicalGaugeBoundaryCompatibility (T).
- 31779 matter_gauge_dirichlet_firewall: 라벨 rfl ∧ Nonempty(MatterField →ₗ CoulombGaugeSlice) := ⟨0⟩ — 영(0) 사상으로 증인. (T, 내용 없음; docstring은 "structural"이라 정직)
- 31794-32393 P1AdmissibleBackgroundExtension: 실제 Mock2 inverse-eta bundle/automorphy factor/eta section, inverseEtaHermitianMetric (|η z|²) transition isometry (field_simp, 진짜 소규모 계산), connection = mfderiv 기반 etaCovariantDerivativeLinear (Mock2 producer). **potential V_Δ = id, g = min(r²,1)** — "safe baseline", 논문의 V_q(augmented-energy Hessian)와 무관함을 docstring이 명시. AdmissibleBackground 구조는 데이터 전용(Prop 필드 없음) — 정직. ModelNotationFirewallCertificate (Prop 구조) 무조건 inhabitant: 필드는 모두 앞선 정리(라벨 rfl, ‖id‖≤1 등) — 대부분 T.
- 32404-32541 EvidenceAccounting: totalEvidenceTagCount=194, links=259 (simp), everyClaim_has_typed_evidence (58/58) — 스캐폴딩. **사소한 불일치**: HasAnyTypedEvidence docstring "ten registries"인데 disjunction은 9개(ClosedPureDiscreteGap 누락) — 결과에는 영향 없음(9개로 이미 커버).
- 32550-33045 IntegratedAxiomAudit: `#print axioms` 424줄 + 주석 (skim).
- 33062-33572 P2ConcreteCuspGeometryExtension: Mock2FA GammaTwoQuotientGeometry의 정리를 별칭으로 재노출하는 facade(A, 1줄 재수출). cusp width 2, 최소성, proper/properly discontinuous action, T2 quotient, open quotient map, compact truncation, frontier null, compact cofinality, flux tail. ConcreteP2GeometryCertificate(Prop 구조, 39필드) 무조건 inhabitant — 모두 import된 정리 (DISCHARGED, 단 실제 증명은 Mock2_FA 쪽). RawFullQuotientPreimageCompactness는 거짓인 강한 명제로 명명만(inhabit 안 함) — 정직.
- 33578-33984 P2IntrinsicTruncatedQuotientExtension: XSet Y = quotient image; preimage = saturation (MulAction.quotient_preimage_image_eq_union_mul), interior ↔ saturation interior (open map, 진짜 소규모 증명), compact/closed/measurable, quotient map (compact→T2), embedding inclusions, exhaustion. raw unclipped cutoff Y≤0 ⇒ 빈 집합 ⇒ "3개 경계성분" 불가 (자명한 no-go, 정직하게 'necessary condition' 표기). (U, 소규모)
- 33999-34931 PolygonTraceExtension: polygon edge pairing 재수출; covariance ⇒ paired-edge multiplier matching (U, 짧음); eta-twisted one-form pullback on edge (U); algebraic oriented normal trace 부호관계 (ring, U); horizontal horocycle 임베딩/C^∞/단위 법선 (U, 초등); width-two 측도·호장 2/H; eta section 수평 제한 ∈ L²([0,2]) (연속⇒유계⇒MemLp, U); trace-enhanced graph closure (bulk ⊕ L² 좌표를 저장하고 closure) — boundary projection 유계는 "구성상"(norm에 포함) — docstring이 "고전적 trace 정리 아님"이라고 명확히 명시(정직). 
- 34945-35686 P2ActualFixedPhaseCuspTraceGraphExtension: 동일 구성을 실제 fixed-phase core(InverseEtaFixedPhaseCore n, GraphSobolevCompletion n)와 3 cusp chart 로 반복. injective, dense, closed kernel, contractive projection. (U, 구성적이지만 trace 추정은 없음 — 정직 명시)
- 35702-36210 P2BoundaryComponentReduction: frontier(XSet) ⊆ image of literal frontier (open map 논증, 진짜), side seam ∪ cusp pieces 포함; PairedSidesBecomeInteriorAt / HorocyclesRemainBoundaryAt 등 명시적 기하 가정(SUBSTANTIVE, 미증명 열린 입력) ⇒ frontier = ⋃ cusp pieces; connectedComponentIn_eq_piece_of_finite_closed_partition (일반 위상 보조정리, 진짜·Mathlib 후보급 소품). ExactThreeCuspBoundaryDecompositionAt = 4개 명제의 ∧ (Iff.rfl). (C)
- 36262-36646 P2ExactThreeBoundaryExtension: **자기 교정**: 이전 강한 side-filling 가정은 corner가 있으면 horocycle survival과 모순(literalFrontierCorners_eq_empty_of_strongSide_and_horocycle) → 즉 앞선 namespace의 가정쌍은 corner 존재 시 SUSPECT-VACUOUS임을 스스로 증명하고 corner 제외 버전으로 교정. 상대내부 lift (U), corrected frontier equality (C), nonempty/disjoint/connected 정확 환원 (U), Y≤1 정규화 cutoff 불변 (U).
- 36663-37095 P2ClassicalTraceBoundaryExtension: ActualFixedPhaseStoredTraceBounded (core trace ≤ C·graph norm) — 핵심 미증명 해석 입력(SUBSTANTIVE, 명시적 Prop, 구조필드 아님). ⇔ continuous extension 존재 (extendOfNorm), unique, ⇔ bulk projection bijective (ContinuousLinearEquiv.ofBijective, Banach inverse) — 진짜 함수해석 논증(U, 조건부 동치). no-go: bound 실패 ⇒ 확장 없음.

## 이어서 (37096–47000)

### 진행 메모 (Read 37096–40943)
- 37096-37346 P2ClassicalTraceBoundaryExtension 끝: §6 "unconditional intrinsic trace-class": K = zero-stored-coordinate 닫힌 부분공간, trace class := Kᗮ, 사영 = orthogonalProjection, 확장 = subtypeL. surjective/contractive/ker=K/dense (Mathlib orthogonal_orthogonal 등). (U, 정확하나 얇음 — 사실상 "임의 닫힌 부분공간의 직교여공간"이라는 일반 Hilbert 사실; docstring이 "H^{1/2}와 동일시 안 함" 명시, 정직). **코드 냄새**: 37219 `noncomputable local instance (priority := 2000)` 로 CLM 타입에 `Norm`을 sInf로 재정의(Mathlib opNorm과 수학적으로 같은 정의이지만 인스턴스 다이아몬드 회피용 해킹; local이라 건전성 영향 없음). actualFixedPhaseStoredTraceComparisonCertificate (37329): bound ↔ extension ↔ bijective 조건부 동치 묶음(U/C).
- 37371-37515 P2RawFullPreimageNogoExtension: 한 점 궤도의 전체 역상이 T^{2n}·I 를 포함 ⇒ re 비유계 ⇒ 비컴팩트 ⇒ ¬RawFullQuotientPreimageCompactness (U, 진짜·초등). 이전 범위에서 "거짓 강명제로 명명만"이라 한 것을 실제 반증으로 종결 — 정직.
- 37531-37721 P2RegularQuotientCoveringExtension: stabilizer-free locus 열린집합(gammaTwoEffective_exists_nhds_image_smul_eq_self 사용), Mathlib isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul 적용 (U). EffectiveActionFree(= IsCancelSMul) 가정판 전역 covering (C) → 바로 다음 namespace에서 **DISCHARGED**.
- 37738-37991 P2GammaTwoFreeActionExtension: **진짜 산술 증명** — Γ(2)의 고정점 원소는 ±1 (ModularGroup.cases_of_mem_fd_smul_mem_fd 의 유한 목록을 mod 2 로 소거 + Gamma_normal 켤레), effective(±1 동일시) 작용은 free (gammaTwoEffective_isCancelSMul 37864), 따라서 ℍ → Γ(2)\ℍ 가 전역 covering map/local homeomorph (37878). quotient ChartedSpace ℍ / ℂ (Classical.choose 로 lift 선택 — 존재 증명 후 선택이라 정당). 수학적으로 참(Γ(2)/±1 은 torsion-free). Mathlib PR 후보급. 단 Γ(2)\ℍ 는 비컴팩트 3-cusp 곡면이며 QYM의 Yang–Mills 내용과는 무관한 배경 기하.
- 38011-38349 P2HorocycleBoundaryMeasureExtension: H⁻¹dx 를 [0,2]에 두고 ℍ, 몫으로 pushforward; 총질량 2/H, 지지집합 (U, 측도론 소규모; quotient measurable structure 사용을 명시). 3개 named cusp 반복.
- 38370-39486 P2ExactBoundaryInhabitantsExtension: **이 범위 최상급 실질 기하**. (i) open map 의 등위점은 닫힌 sublevel 내부 불가(일반 보조정리 38490); (ii) 각 coset에 명시적 cusp 점 ⇒ 3 cusp part nonempty (upstairsCuspFrontierPartsNonempty 38771, 이전 가정 DISCHARGED); (iii) Ford-horoball 추정 `modular_lowerLeft_eq_zero_of_im_eq_of_one_lt` (38790: im>1 보존 ⇒ c=0) + mod 2 첫 열 ⇒ level>1 에서 cusp 간 궤도 분리 (noCrossCuspOrbit_of_one_lt_level 38943, DISCHARGED); (iv) fd 에서 1/Im<2 (38984, √3/2 대신 거친 상수 — 정직 명시) ⇒ level≥2 에서 horocycle 이 경계로 남음 (cuspSaturationRemainsNonInterior_of_two_le_level 39071, DISCHARGED) 및 paired side 가 내부가 됨 (39159, DISCHARGED). 최종 `exactThreeCuspBoundaryDecomposition_of_two_le_level_from_connectedness` (39446): level≥2 에서 **연결성(CuspBoundaryPiecesConnectedAt) 한 가지만 가정**(C, SUBSTANTIVE·참으로 보임). relativeInterior/individual frontier no-go (ℝ 1점/반직선, T 수준 교육용 반례).
- 39518-40525 P2NormalGreenExtension: edge 파라미터 변환(t↦-t) 하 Bochner 적분 불변 (Homeomorph.neg measurableEmbedding, 비적분 분기 포함), η-twisted one-form 법선미분 짝맞춤 ⇔ opposite normal pushforward (A 비퇴화 시), **edge pairing 이 involution 임을 right-coset 계산으로 증명** (40315; 원형 변 S⁻²=-1∈Γ(2)), 짝 seam flux 상쇄, 전체 edge 합 = 0 (40418). 미증명 입력 `ActualPairedEdgeVelocityChainRule` (40080, 변 곡선 derivWithin 의 chain rule — SUBSTANTIVE, 참일 것이나 표준 미분 계산으로 증명 가능한데 미증명), `HasOppositePairedNormalPushforward` (SUBSTANTIVE). docstring 40508-40523 이 남은 3단계(velocity, outward normal, curvilinear Stokes)를 명시 — 정직. greenBoundaryDefect=0 은 주장하지 않음.
- 40549- P2ClassicalHhalfTraceExtension 시작: Mathlib에 없는 원 위 분수 Sobolev H^{1/2}를 twisted Slobodeckij 몫 |Δf|/d_circ ∈ L²([0,2]²) 로 직접 정의 (s=1/2 ⇒ 1+2s=2, 정의 충실). 선형성/반대칭/가측성, Lipschitz+quasi-periodic ⇒ 유한 H^{1/2} 에너지 (40908, U, 초등이지만 진짜).

### 진행 메모 (Read 40943–43317)
- 40943-42395 P2ClassicalHhalfTraceExtension (계속): a.e. 불변성(product quasiMeasurePreserving), widthTwoHhalfDomain (Submodule, carrier = MemLp 조건 — 구조 필드 아닌 성질정의), Gagliardo 에너지 lintegral 유한성, graph map → WithLp 2 (L² × L²) → topologicalClosure 로 Hilbert 완비화, contractive forgetful map. **실제 inverse-eta 전이함수** actualFixedPhaseCuspBoundaryTransition (41343, η(z)/η(z+2)·denom^{2n}) 연속·비영, smooth core trace 의 정확한 quasi-periodicity (41437, 코어 공변성에서 유도), cusp 곡선 C^∞ (Möbius 유리함수 계산 41497), trace 의 C^∞ ⇒ compact Lipschitz ⇒ **모든 smooth core trace 의 H^{1/2} 에너지 유한** (41604/41630, actualFixedPhaseHhalfFiniteEnergyCore_eq_top 41741). 3-cusp H^{1/2} target, bulk×H^{1/2} enhanced graph, dense core. `actualFixedPhaseHhalfTraceBound_iff_exists_extension` (42347): 핵심 trace 추정(‖Tr u‖_{H^{1/2}} ≤ C‖u‖_graph) ⇔ 유계 확장 존재 — 양쪽 모두 미증명, 가설/필드로 들여오지 않고 docstring(42367-42393)에 "남은 해석적 명제 + 확장 right-inverse"로 명시. 정의 충실도 높음(진짜 Slobodeckij), 단 클래식 trace 정리는 미증명.
- 42416-42799 P2SmoothCuspBoundaryExtension: cusp segment closed embedding (compact→T2), C^∞ coordinate, scaling chart 에서 수평 ⇒ 접선 1, outward normal I·level (Im 증가로 바깥쪽임을 증명), 쌍곡 직교·단위 노름 (U, 초등). IsSmoothCoordinateClosedEmbeddedSegment 는 Prop 구조이나 모든 필드를 정리로 채움(DISCHARGED).
- 42818-43301 P2ConnectedCuspComponentsExtension: **마지막 연결성 가정 제거**. SL(2,ZMod 2) (6원소) 에서 같은 cusp label ⇒ A=C 또는 A=C·T (`decide`, 소형·건전), 같은 class 의 quotient loop range 동일, Im≥2 에서 c≠0 이면 높이 ≤1/2 < fd 높이 ⇒ bridge 상삼각 ⇒ loop 의 모든 점이 active frontier arc 에 대표원 보유 ⇒ quotient cusp piece = 연속 loop 의 range ⇒ connected. **`exactThreeCuspBoundaryDecomposition_of_two_le_level` (43286) / `_of_two_le_cutoff` (43293): Y≥2 에서 Γ(2)\ℍ 절단의 frontier 가 서로소·비어있지 않음·연결된 3개 cusp horocycle 의 합집합임을 무조건 증명 (U, 진짜 쌍곡기하·산술).** 앞서 SUBSTANTIVE 로 분류된 PairedSides…/HorocyclesRemainBoundary…/NoCrossCuspOrbit…/Connected… 4개 입력이 Y≥2 에서 모두 DISCHARGED. Y∈(1,2) 는 여전히 조건부(정직).

### 진행 메모 (Read 43318–47015)
- 43318-43728 P2HhalfClosabilityExtension: **twisted difference quotient 의 closability 증명** — L² 수렴 ⇒ 측도수렴 ⇒ a.e. 부분수열(두 번), product projection quasiMeasurePreserving 으로 null 집합 끌어옴, 점별 연속성 ⇒ g=0 (43403). tau 가 가측일 필요도 없음. ⇒ graph closure 의 첫 사영 단사 (43614), range 위에서만 대수적 역(연속 역 주장 안 함, 정직). (U, 진짜 해석). WidthTwoHhalfFiniteEnergyDomainDense 는 이 시점 Prop 로 분리 → 46132 에서 DISCHARGED.
- 43745-44330 P2ExplicitEdgeVelocityExtension: 3종 base edge (원호/좌우 수직선) 의 명시적 도함수(√ 분기 포함), Möbius 도함수 1/(cz+d)² (UpperHalfPlane.hasStrictDerivAt_smul), derivWithin = deriv (내부점), 짝 identity 미분 ⇒ **`actualPairedEdgeVelocityChainRule` (44273) — 39780 의 미증명 입력 DISCHARGED**. 접선 비영 (U).
- 44335-44645 P2HhalfDensityExtension: η-전이함수 C^∞ (ModularForm.differentiableAt_eta…, 복소 해석 → 실 C^∞), 내부 지지 smooth 함수의 covariant doubling ⇒ 유한 H^{1/2} 에너지; Mathlib Lp.dense_hasCompactSupport_contDiff. 내부지지 core 밀도는 Prop 로 분리 → 46126 DISCHARGED.
- 44662-45129 P2ExplicitEdgeNormalExtension: 명시적 쌍곡 단위 법선 (y/‖w‖)(−I)w, 단위·직교·우측(=저장된 orientation 기준 바깥쪽 — 저장 orientation 이 양의 방향임은 별도 증명 안 됨, "outward" 는 docstring 조건부 명명), d1-차트에서 짝 음법선 법칙 (U). mfderiv 판은 ActualNormalManifoldD1Compatibility ⇔ 로 환원 → 45744 DISCHARGED. zeroEdgeNormalField 도 bare pushforward 명제를 만족함을 명시(약한 명제 오용 방지 — 정직, 좋은 관행).
- 45134-45621 P2SmoothQuotientAtlasExtension: 높이≥2 cusp loop 가 AddCircle 2 로 내려가 **단사**(Ford 추정+Γ(2) 짝수 translation, 45275) ⇒ closed embedding ⇒ 각 경계성분 ≅ 원 (45429). C⁰ local diffeo, all-sheets atlas, SmoothTransitionResidual (Prop) 가정 하 IsManifold (C), CuspCollarResidual (Prop) 정의.
- 45640-45785 P2ManifoldD1BridgeExtension: extChartAt 이 포함사상임을 rfl 로, mfderiv = 1/(cz+d)² (45704), mfderiv = d1 ⇒ 법선 pushforward 무조건 (45751). (U)
- 45790-46141 P2HhalfCollarDensityExtension: ContDiffBump 기반 χ_n = β/(β+1/(n+1)), a.e. 수렴 + uniform integrability (tendsto_Lp_finite_of_tendsto_ae) ⇒ L² 수렴 ⇒ 내부 core 조밀 (46115) ⇒ **실제 η-전이 H^{1/2} 유한에너지 도메인 조밀 (46132, 무조건)**. (U, 진짜 측도론)
- 46156-46476 P2SmoothTransitionClosureExtension: sheet transition 이 각 점에서 어떤 Γ(2) 원소와 일치, local injectivity ⇒ 일치 locus 열림 ⇒ 국소적으로 Möbius ⇒ 매끄러움 ⇒ **SmoothTransitionResidual DISCHARGED (46365), `gammaTwoQuotient_isManifold` (46412): Γ(2)\ℍ 위 complex-smooth(=정칙) IsManifold 𝓘(ℂ) ∞ 무조건**. SmoothQuotientAtlasCertificate (Prop 구조) 정리로 채움. **코드 냄새**: 37955 에 전역 instance `gammaTwoQuotient_chartedSpaceH`(선택 lift atlas) 가 있고, IsManifold 는 letI 로 다른 atlas(allCoveringSheetsChartedSpaceH)에 대해서만 증명 — 동일 타입 위 두 ChartedSpace 구조(chartAt 동일, atlas 상이) 공존; 건전성 문제는 아니나 비정규 인스턴스.
- 46496-47015 P2CuspCollarClosureExtension (범위 경계에서 중단, 이후는 다음 범위): ℝ×(1,∞) → ℍ open embedding, cusp cylinder AddCircle 2 × (1,∞) → 몫 의 단사(Im>1 끼리면 c=0, 47805) / open map ⇒ open embedding (46950), band 반경 1/2. CuspCollarResidual 의 discharge 는 47000 이후.

## 범위(37096–47000) 요약

### 헤드라인 정리 (U=무조건 진짜, C=조건부, A=accessor, T=자명)
| 줄 | Lean 이름 | 내용 | 상태 |
|---|---|---|---|
| 37507 | not_rawFullQuotientPreimageCompactness | 원시 전역 역상 컴팩트성 반증 | U(초등) |
| 37864/37878 | gammaTwoEffective_isCancelSMul / gammaTwoQuotientMk_isCoveringMap | Γ(2)/±1 작용 free, ℍ→Γ(2)\ℍ covering | U(진짜 산술) |
| 38943 | noCrossCuspOrbit_of_one_lt_level | level>1 cusp 간 궤도 분리 | U |
| 39071/39159 | cuspSaturationRemainsNonInterior_of_two_le_level / pairedSidesAwayFromHorocyclesBecomeInterior_of_two_le_level | horocycle 경계 유지·변 내부화 | U |
| 43286 | P2ConnectedCuspComponentsExtension.exactThreeCuspBoundaryDecomposition_of_two_le_level | Y≥2: frontier(X_Y) = 서로소·비공·연결 3 cusp 성분 | **U(범위 최고 성과)** |
| 45429 | selectedCuspCircleHomeomorphBoundaryPiece | 각 성분 ≅ AddCircle 2 | U |
| 46412 | gammaTwoQuotient_isManifold | Γ(2)\ℍ 정칙 다양체 구조 | U |
| 40418 + 44273 | all_orientedEdgeFluxIntegrals_eq_zero + actualPairedEdgeVelocityChainRule | 불변 flux 의 seam 적분 상쇄 (속도 chain rule 은 이후 discharge) | U(결합) |
| 41741 | actualFixedPhaseHhalfFiniteEnergyCore_eq_top | 모든 smooth core trace 가 진짜 H^{1/2} | U |
| 43403 / 46132 | widthTwoHhalfDifferenceToL2_sequentiallyClosable / actualFixedPhase_widthTwoHhalfFiniteEnergyDomainDense | H^{1/2} graph closability, 도메인 조밀 | U |
| 42347 | actualFixedPhaseHhalfTraceBound_iff_exists_extension | 핵심 trace 추정 ⇔ 유계 trace 확장 | C(동치만, 양변 미증명) |
| 37312 | actualFixedPhaseCanonicalTraceClassCertificate | 닫힌 부분공간 직교여공간 = "trace class" | U이나 얇음(명칭 과장 소지) |

### 조건부 입력 분류 (이 범위)
- DISCHARGED (같은 범위 안에서): EffectiveActionFree(37668→37864), UpstairsCuspFrontierPartsNonemptyAt(38771), NoCrossCuspOrbitAt(level>1), CuspSaturationRemainsNonInteriorAt·PairedSidesAwayFromHorocyclesBecomeInteriorAt(level≥2), CuspBoundaryPiecesConnectedAt(43267), ActualPairedEdgeVelocityChainRule(44273), ManifoldDeckDerivativeD1Compatibility(45744) ⇒ HasOppositePairedNormalPushforward(45751), WidthTwoInteriorSmoothL2CoreDense(46126) ⇒ WidthTwoHhalfFiniteEnergyDomainDense(46132), SmoothTransitionResidual(46365). 이 "Prop 로 분리 → 다음 Extension 에서 증명" 패턴이 일관되고 정직함.
- SUBSTANTIVE (미해결): ActualFixedPhaseStoredTraceBounded / H^{1/2} trace 추정(42347; 고전 trace 정리의 graph-norm 판), 확장 right-inverse, curvilinear Stokes/divergence (40508-40523 docstring 명시), level∈(1,2) 의 side-filling/cusp-exterior/연결성, CuspCollarResidual(47000 이후 처리 예정).
- CIRCULAR: 이 범위에서 발견 안 됨. SUSPECT-VACUOUS: 이전 범위의 strong side-filling 쌍(36262- 자기교정)만; 이 범위 신규 없음.
- reference/degenerate instance: 없음. zero 필드 (zeroEdgeNormalField 45110) 는 오히려 약한 명제 경고용으로 사용.

### Yang–Mills / mass gap
- **37096–47000 에는 Yang–Mills·질량간극 주장(무조건/조건부/toy) 이 전혀 없음.** 전부 "P2" 배경 기하·해석(Γ(2)\ℍ 절단 영역, cusp 경계, trace, H^{1/2}, Green seam) 이다. 이는 논문의 gauge slice 도메인 X_Y 를 위한 토대이며, q-YM 범함수·Hamiltonian·spectral gap 과의 연결은 이 범위에 없음.

### 정의 충실도
- 높음: Γ(2) 작용/몫 (Mathlib CongruenceSubgroup, MulAction quotient), η 승수 (Mathlib ModularForm.eta), IsCoveringMap/IsManifold (Mathlib), 측도 pushforward, Slobodeckij H^{1/2}(1D, s=1/2 지수 정확), mfderiv.
- 대리/명칭 주의: canonical trace class(Kᗮ), stored L² trace target, "outward" 는 저장 orientation 기준.

### 실질 수학 비율 (37096–47000, 9905줄)
- 빈 줄 1126 (11%), 주석/docstring 1423 (14%), `#print axioms` 167 (2%), 코드 7189 (73%). 코드 중 집계용 certificate 정리·별칭·얇은 래퍼 ≈ 15%. ⇒ **진짜 수학 ≈ 60%** (QYM 전체 중 가장 높은 구간). decls 653개(정리 462) 중 accessor 0, 15줄 이상 정리 159.

### 수학적 정확성
- 오류 발견 없음. 과장 소지: (i) "unconditional intrinsic trace-class" (37106) — 일반 Hilbert 사실의 재명명; (ii) "outward" 법선 — orientation 양성 미증명(docstring에 조건 명시); (iii) `one_div_im_lt_two_of_mem_fd` 는 의도적으로 거친 상수(정직 표기).

### 코드 품질
- 단점: `Mock2FA.PaperCorrections.AutomorphicSobolev.GammaTwoQuotientGeometry.` 등 완전수식 이름을 `open` 후에도 수백 회 반복; namespace 뒤 10~16줄 빈 줄 반복; 3 cusp 별 동일 증명 반복; 37219 Norm local instance 해킹; 동일 타입 위 두 ChartedSpace; Extension 레이어를 계속 덧붙이는 구조(앞 namespace 의 Prop 를 뒤 namespace 가 discharge) — 리팩터링 없이 누적. 167 `#print axioms`.
- 장점: 증명 자체는 견고(긴 calc, 명시적 보조정리), 0 accessor, 0 sorry. Mathlib PR 후보: Γ(2)/±1 free action·torsion-free (37770-37867), open-map 등위점 비내부 보조정리 (38490), Ford horoball 추정 (38790/43080), 일반 difference-quotient closability, finite closed partition 연결성분 (이전 범위).

## 범위 전체(31401–47000) 종합 및 잠정 점수
- 31401–37095 (이전 감사자): P1 matter-gauge firewall (영 사상 증인, T), AdmissibleBackground (V=id, g=min(r²,1) — 논문 V_q 와 무관함을 정직 명시), EvidenceAccounting 스캐폴딩, `#print axioms` 424줄 블록, Mock2_FA 재수출 facade(A), trace-enhanced graph closure (trace 유계는 "구성상"), BoundaryComponentReduction 의 명시 가정 + 자기교정. 진짜 비율 ≈ 40%.
- 37096–47000: 위와 같이 ≈ 60%, 대부분 무조건 진짜 증명.
- **전체 31401–47000 진짜 수학 ≈ 50–55%.** Yang–Mills/mass-gap 관련 주장은 전 범위에 실질적으로 없음(유일한 P1 항목은 영 사상 증인의 T 수준).

| 축 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 9 | sorry/axiom 0, 컴파일 확인, decide 는 6원소 SL(2,ZMod 2)·소형뿐, Classical.choose 는 존재증명 후; local Norm 인스턴스·이중 ChartedSpace 는 냄새일 뿐 |
| 조건부 인증 정직성(비순환성) | 8 | 순환 가설 없음; 잔여 입력을 Prop 로 노출 후 대부분 실제 discharge; 자기교정 사례; 감점: "unconditional/certificate" 명칭이 얇은 결과에도 붙음, P1 영 사상 증인 |
| 수학적 실질성 | 7 | Γ(2) torsion-free·covering·정칙 다양체·정확한 3-cusp 경계·H^{1/2} closability/density 는 진짜; 그러나 결정적 해석 입력(graph-norm trace 정리, curvilinear Stokes)은 미해결이고 YM 내용과 무관 |
| 정의 충실도 | 8 | Mathlib 의 실제 개념 사용, Slobodeckij 정의 정확; Kᗮ trace class·stored L² target·V=id 는 명시된 대리 |
| 코드 품질·유지보수성 | 5 | 과도한 완전수식명·빈 줄·반복·누적식 Extension 레이어·#print axioms 수백 줄; 단 증명 구조는 견고, upstream 후보 다수 |
| 종합 | 7 | QYM 중 가장 견실한 구간이나, 논문의 주장(질량간극)과는 거리가 먼 배경 기하·함수해석 토대 |

### 커버리지 로그 (이 감사자)
- 정독: 37096–38094, 38095–39094, 39095–40043, 40044–40943, 40943–41792, 41793–42492, 42493–43322, 43318–44117, 44117–44916, 44917–45676, 45676–46495, 46496–47015 (전 범위 순차 Read; `#print axioms` 블록은 읽었으나 내용 무의미).
- 통계: python 으로 원본/주석제거본 비교(빈 줄·주석·#print axioms·코드), decls_cls.json 필터(QYM, 37096–47000).
