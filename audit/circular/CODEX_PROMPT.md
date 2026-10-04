# Codex 작업 프롬프트 — 순환·공허 정리 수정

아래 `---` 사이의 내용을 Codex에 그대로 붙여 넣으세요.

---

## 역할과 목표

당신은 Lean 4 / Mathlib 형식화 저장소를 정비하는 엔지니어입니다. 저장소 `leegahuyn/mathlib4`의 `PrimalitySheafVerification/` 13개 모듈에서 **순환 정리**와 **공허 정리**를 체크리스트에 따라 하나씩 수정합니다.

- **순환 정리**: 가설이 곧 결론인 정리
- **공허 정리**: 거짓이거나 만족할 수 없는 가설 위에서 성립하는 정리

목표는 수학적으로 **정직한** 저장소입니다. 형식적으로 더 많은 정리를 통과시키는 것이 목표가 아닙니다. 진짜로 증명된 수학은 하나도 잃지 않아야 하고, 모든 모듈은 계속 오류 0으로 컴파일되어야 합니다.

## 0. 준비

1. 작업 기준은 태그 `formalization-final-authority-2026-08-21`입니다. 여기서 새 브랜치 `fix/circularity-2026-10`을 만드세요.
2. 감사 자료를 저장소 루트의 `audit/`로 가져오세요.
   - 출처: `leegahuyn/FORMALIZATION-OF-MY-10-PAPERS` 브랜치 `claude/kind-archimedes-a5duv9`의 `audit/circular/`와 `audit/verification/`
   - 결과 경로: `audit/circular/…`, `audit/verification/…` (디렉터리 구조를 유지해야 합니다. `circularity_lint.py`가 `../verification/lean_scan.py`를 import합니다.)
3. 다음 파일을 먼저 읽으세요.
   - `audit/circular/README.md` (분류 근거)
   - `audit/circular/CHECKLIST.md` (자동 탐지 191개, ID C001–C191)
   - `audit/circular/SUPPLEMENTARY.md` (자동 탐지 밖 62개, ID S001–S062)
   - 필요하면 원 감사 보고서 `audit/README.md`와 `audit/modules/*.md`도 참고하세요. 같은 브랜치에 있습니다.
4. 툴체인은 `leanprover/lean4:v4.33.0-rc1`입니다.
   - Mathlib는 상류 커밋 `93594942`와 동일합니다. 먼저 `lake exe cache get`을 시도하세요.
   - 실패하면 `lake build Mathlib`로 소스 빌드하세요(4코어 기준 약 35분).
5. **기준선을 기록하세요.** 아래 §5의 검증 명령을 수정 전에 한 번 실행하고, 결과를 `audit/circular/FIX_REPORT.md`의 "Before" 절에 적으세요.
   - 기대값: 컴파일 오류 0, 오염 상수 0, 린트 191개(허용 목록 적용 시 141개 표시)

## 1. 용어와 판정 기준

- **순환(CIRC)**: 가설에서 결론이 `h`, `h x`, `h.1`, `Iff.rfl`, `le_trans` 한 단계 정도로 바로 나오는데, 그 정리를 논문 결과(Theorem/Prop/Claim/Remark)나 "조건부 인증"으로 내세우는 경우입니다. 구조체 필드가 곧 결론인 인증서를 쓰는 정리도 여기에 포함됩니다.
- **공허(VAC)**: 가설·인터페이스가 거짓이거나 만족 불가능한 경우입니다. 예: `audit/verification/Spt7Vacuity.lean`이 증명한 `ModuleDepthDimensionInterface`.
- **동어반복 프록시(PROXY)**: `etalePiece := goodOpen`처럼 정의를 펼치면 결론이 나오는 것을 논문의 실질 결과로 표기한 경우입니다.
- **원장 오표기(LEDGER)**: String/Bool 원장, `ClaimStatus` 같은 상태 열거형, 헤더 주석, 독스트링이 실제 내용과 다르게 "UNCONDITIONAL / proved / certified / satisfiedByLean" 등으로 표기한 경우입니다.
- **허용되는 조건부 정리**: 외부 입력 가설(예: `SatisfiesHasse E`)을 받되, 결론이 그 가설보다 **실질적으로 더 많은 것**을 말하는 정리입니다. 가설과 결론이 같은 래퍼 정리는 허용하지 않습니다.

## 2. 항목별 결정 규칙

각 항목은 다음 중 **정확히 하나**로 처리하고, 체크리스트에 결과를 기록하세요.

| 결과 | 언제 | 해야 할 일 |
|---|---|---|
| `FIXED-PROVED` | 가설을 실제로 증명할 수 있을 때(파일 안 기존 결과나 Mathlib 사용) | 가설을 증명으로 해소하고, 가설 없는 무조건 정리로 바꿉니다. 이름에서 `_of_…`/`conditional`을 정리합니다. |
| `FIXED-RESTATED` | 진술 자체가 틀렸거나(예: GK가 X를 제약하지 않음) 가설이 결론과 같을 때 | 수학적으로 올바른 진술로 고칩니다. 더 약하고 결론과 구별되는 가설로 바꾸거나 실제 대상을 연결합니다. 그다음 증명합니다. |
| `DELETED` | 내용이 없고(래퍼, 동어반복, 공허), 해소도 어려울 때 | 선언을 삭제하고 **모든 사용처**를 고칩니다(아래 §3.4). |
| `RENAMED-API` | 정의의 정상 분해 보조정리인데 논문 결과처럼 이름이나 라벨이 붙었을 때 | `Foo_def`/`Foo_iff`/`Foo.field` 형태로 개명하고, 논문 라벨과 원장의 "증명됨" 표기를 제거합니다. |
| `ISOLATED` | B 분류(재진술 분해)를 당장 삭제하면 연쇄가 너무 클 때 | `…Scaffolding` 네임스페이스로 옮기고 독스트링에 "퇴화 reference 데이터의 재진술 — 증거 아님"을 명시합니다. `allowlist.txt`에 `# 사유`와 함께 추가하고, 원장에서 증거 집계를 뺍니다. |
| `KEPT` | C·D 분류이거나, 확인해 보니 실질적인 외부 입력일 때 | 근거를 한 줄로 적습니다. D는 가설 없는 따름정리를 추가합니다. |

**분류별 기본 방침**

- **A(10개)**: `FIXED-PROVED` > `FIXED-RESTATED` > `DELETED` / `RENAMED-API` 순으로 시도합니다.
- **B(131개)**: `DELETED`를 우선하고, 연쇄가 크면 `ISOLATED`로 처리합니다.
- **C(46개)**: `KEPT`입니다. 확인만 하고, 중복이 있으면 합칩니다.
- **D(4개)**: `KEPT`하고 무조건 따름정리를 추가합니다.
- **S(62개)**: 위 표를 적용합니다. `VAC` 항목은 반드시 `DELETED` 또는 `FIXED-RESTATED`로 처리합니다. 거짓 가설을 남기면 안 됩니다.

## 3. 반드시 지킬 규칙

1. **탈출구 금지**: `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`, `set_option maxHeartbeats 0`, `debug.skipKernelTC`, 새 `elab`/`macro`를 쓰지 마세요.
2. **새 순환을 만들지 마세요.** 수정 후 린트에서 새 항목이 생기면 안 됩니다.
3. **진짜 수학 보존**: 아래 선언(이름 기준, 네임스페이스는 grep으로 확인)은 삭제하지 말고, 계속 컴파일되게 하세요. 진짜 증명을 담은 다른 선언도 삭제 대상이 아닙니다.
   - `tor1_obj_iso` (Spt1, Spt3)
   - `ProjRes.torFullIso` (Spt6)
   - `abstractTorOneIsoGcd` (Spt7)
   - `mathlibTor1ZIsoCyclicModel` (Mock2)
   - `formallyEtale_iff_squarefree_of_ne_zero`, `kaehlerEquivJacobianQuotient` (Spt2)
   - `fullThetaCovariance`, `gamma2_eq_closure_standard_generators` (Mock2_Advanced)
   - `eta_transform`, `adjoint_adjoint_eq_closure` (Mock2_FunctionalAnalysis)
   - `gammaTwoQuotient_isManifold`, `exactThreeCuspBoundaryDecomposition_of_two_le_level` (QYM)
   - `advanced_claims_ii_ramanujan_f_prefix_table` (Mock1_Advanced)
4. **사용처 추적**: 선언을 삭제하거나 개명하기 전에 `grep -rn "<name>" PrimalitySheafVerification/`로 **모든 모듈**의 사용처를 찾아 함께 고치세요. 모듈 간 의존이 있습니다.
   - Mock2 → Mock2_FunctionalAnalysis_Integrated → QYM → Mock3 → BuildAll
5. **원장 동기화**: 이름이나 상태가 바뀐 정리는 다음 위치에서도 모두 갱신하세요. 상태 값은 그 파일에 이미 있는 생성자(`conditional`, `notClaimed`, `futureWork`, `assumedExternal` 등)를 우선 쓰세요.
   - String 레지스트리 (`grep -n '"<name>'`)
   - 상태 열거형 분류 정리
   - 헤더 주석, 독스트링
   - Spt3 `#assert_spt3_certified_safe_axioms` 목록과 `spt3Boundary`
6. **범위 밖 수정 금지**: `Mathlib/`, `lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `.github/workflows/`는 건드리지 마세요.
7. **실패 시 처리**: 증명이 막히면 `sorry`로 남기지 마세요. `DELETED`, `RENAMED-API`, `ISOLATED` 중 정직한 쪽을 선택하고, 사유를 기록하세요.

## 4. 항목별 구체 지침

- **C001 `ec_hasse`, C010 `thm836_part2`**
  - 둘 다 독스트링은 "의도적으로 조건부"이지만 래퍼가 결론과 같습니다.
  - Mathlib에 Hasse 한계나 등차수열 소수의 밀도 정리가 있는지 확인하세요. 있으면 `FIXED-PROVED`로 처리합니다.
  - 없으면 래퍼 정리를 `DELETED`하고, 이름 붙은 가설(`SatisfiesHasse`, `DirichletDensityAP`)만 외부 입력으로 남기세요.
- **C003 + S003 GK**
  - `GoldwasserKilianPropagationTheorem`의 진술은 `ECStepCertificate E X`가 X를 제약하지 않아 거짓으로 보고되었습니다.
  - 인증서가 ZMod X 위의 곡선, 점 위수 조건 등으로 X를 실제로 제약하도록 `FIXED-RESTATED`하세요. 그게 어렵다면 GK 정의, `sound_of_GK`, `theorem1_via_GK_step`과 그 체인을 `DELETED`하세요.
- **C005 + S002 `MtALogInput`**
  - `Λ = padicLog1p u`(파일 내 정의)에 대해 파일의 `padicLog1p` 노름 상계로 해소할 수 있는지 시도하세요(`FIXED-PROVED`).
  - 불가하면 `rmk2_2_uniform_remainder`를 `DELETED`하세요.
- **C007, C009, S013, S014, S019 (Spt3 Theorem 18)**
  - `prime_iff_section_of_complete`, `theorem18_of_any_complete`, `global_certificate_conditional`, `certification_iff_of_complete`는 `DELETED`하거나 `_of_assumed_complete`로 개명한 뒤 인증·경계 목록에서 제거하세요.
  - `theorem18_unconditional`은 "Lucas 판정법 재진술"로 정직하게 라벨링하고, 원장끼리의 모순을 해소하세요.
- **C011 `claim91_necessary`**: `goodReduction_iff_not_dvd`로 `RENAMED-API` 처리하고 "Claim 9.1" 라벨을 제거하세요.
- **C013 `goodOpen_to_etalePiece`**: `etalePiece := goodOpen` 프록시를 제거하거나 "모델"로 명시하세요.
- **C014 `CoeffAgreement`**: 정의를 삭제하고 사용처를 `p = q`로 바꾸세요. 원장 `status_padicLog_fms_coefficient_rigidity`도 수정하세요.
- **C156 + S058 (Mock2 Lemma 6.1)**: 추상판(`modularCovariance_restrict`, `lemma6_1_covariance_restrict`, `lemma6_1_qGauge_certificate`)을 기하판 `lemma6_1`(Mock2 17325 부근, 실제 증명)로 대체하거나 `DELETED`하세요.
- **S042 (Spt7 Prop .18)**
  - `ModuleDepthDimensionInterface`, `ENatDepthDimensionAPI`와 이를 가정하는 `prop18_*` 약 160개, `ActualDepthDimensionPackage`를 `DELETED`하세요.
  - 대안으로, 진짜 depth 개념(Mathlib 정칙열 이론)으로 정의를 바꿔 만족 가능하게 고칠 수 있습니다(`FIXED-RESTATED`). 이 경우 `audit/verification/Spt7Vacuity.lean`과 같은 방식으로 새 인터페이스가 **만족 가능함**을 보이는 인스턴스를 하나 이상 만드세요.
  - `Spt7Vacuity.lean`은 구조체를 복사해 둔 독립 파일이므로 그대로 둬도 됩니다.
- **S043 (Spt7 Equivalence C, "RH ⟺ TP")**: 임의의 `Prop` RH/TP를 쓰는 체인을 `DELETED`하세요. 그러면 Spt7 게이트 분해 정리 B 7개는 `ISOLATED`나 `DELETED`로 정리할 수 있습니다.
- **S052 (Mock1_Advanced 엔트로피 입력)**: 상수를 α = π/√6, β = −log 2로 고치거나 `DELETED`하세요. 고친다면 구간 증명도 갱신해야 합니다.
- **B (Mock1_Advanced 121개) + S053–S057**
  - `PaperInstancesHRlf*Statement`, `AdvancedClaimsII*PromptObjective`, `AdvancedClaimsIIRlf*MathStatement`와 그 `_at` 분해 정리, 그리고 이를 소비하는 readiness/ledger 체인을 가능한 한 통째로 `DELETED`하세요.
  - 다음은 **유지**하세요: 실제 Ramanujan f(q) 계수(68251–68301), 논문 반증 정리들(64710–69714), Bool manifest(70934–70952).
  - `EnvironmentPinManifest`(12114)는 삭제하거나 실제 값으로 고치세요.
- **S018 (Spt3 거짓 `hB`)**: `amalgam_isSheaf` 계열을 삭제하고, 사용처를 `RepointedConst_isSheaf`(4691)로 교체하세요.
- **S040 (Spt6 형식 로그)**: 주석 처리된 7867–7954를 살려 실제로 증명하거나(Mathlib `PowerSeries` 로그 사용), 원장의 `.unconditional`을 고치세요. `example : True := trivial`은 제거하세요.

## 5. 검증 명령 (모듈 하나를 수정할 때마다)

```bash
O=.lake/build/lib/lean/PrimalitySheafVerification; mkdir -p $O
# 수정한 모듈과 그 하류만 다시 컴파일해도 됩니다. 최종 확인은 전체 순서로 하세요.
for m in Spt1 Spt2 Spt3 Spt4 Spt5 Spt6 Spt7 Mock1 Mock1_Advanced Mock2 Mock2_Advanced \
         Mock2_FunctionalAnalysis Mock2_FunctionalAnalysis_Integrated QYM Mock3 BuildAll; do
  lake env lean -DmaxErrors=2000 -o $O/$m.olean -i $O/$m.ilean PrimalitySheafVerification/$m.lean > /tmp/$m.log 2>&1
  echo "$m exit=$? errors=$(grep -c ': error' /tmp/$m.log) sorry=$(grep -c "declaration uses 'sorry'" /tmp/$m.log)"
done
lake env lean audit/verification/AxiomAudit.lean   # tainted 0, canary는 sorryAx로 계속 검출되어야 함
python3 audit/circular/circularity_lint.py PrimalitySheafVerification --allow audit/circular/allowlist.txt
mkdir -p /tmp/scan && python3 audit/verification/lean_scan.py PrimalitySheafVerification /tmp/scan   # 탈출구 토큰이 0인지 확인 (/tmp/scan/stats.json)
```

참고 시간(4코어 기준): Mock2_FunctionalAnalysis 약 13분, QYM 약 20분, Mock1_Advanced 약 10분, 나머지는 각 1–7분입니다.

## 6. 기록과 커밋

- `CHECKLIST.md`와 `SUPPLEMENTARY.md`의 각 줄을 다음 형식으로 갱신하세요.
  - `- [x] **C003** … — 결과: DELETED (GK 진술이 X 미제약으로 거짓; sound_of_GK, theorem1_via_GK_step 함께 삭제)`
- **커밋은 모듈 단위로** 하세요. 메시지 예: `Spt3: remove circular Theorem-18 wrappers (C007, C009, S013, S014, S019)`
- 모든 커밋 시점에서 그 모듈과 하류가 컴파일되어야 합니다.
- 브랜치 `fix/circularity-2026-10`에 푸시하세요. PR은 만들지 마세요. 사용자가 검토합니다.

## 7. 완료 기준 (모두 충족해야 끝)

1. `CHECKLIST.md` 191개와 `SUPPLEMENTARY.md` 62개가 **모두 `[x]`이고 결과가 기록**되어 있습니다.
2. 16개 컴파일 대상이 모두 exit 0, 오류 0, `declaration uses 'sorry'` 0입니다.
3. `AxiomAudit.lean`: 비표준 공리 오염 0이고, 카나리아는 계속 검출됩니다.
4. 린트(허용 목록 적용)가 exit 0입니다. 처음 C·D 50개 외에 허용 목록에 추가한 항목은 모두 `# 사유` 주석이 있습니다.
5. 탈출구 토큰 수가 기준선(전부 0)에서 늘지 않았습니다.
6. 순환·공허 가설에 기대는 결과를 "unconditional / proved / certified"로 표기하는 원장, 독스트링, 헤더가 남아 있지 않습니다.
7. §3.3의 진짜 수학 선언이 모두 존재하고 컴파일됩니다.
8. `audit/circular/FIX_REPORT.md`에 다음을 작성했습니다.
   - Before/After 수치: 린트 hit 수, 선언 수, 정리 수, 줄 수
   - 삭제된 선언 목록, 개명 목록(구 → 신), 원장 변경 목록
   - `FIXED-PROVED`로 새로 증명한 정리 목록
   - 남은 외부 입력 가설 목록(이름, 위치, 왜 실질적인지)
   - 하지 못한 항목과 이유

---
