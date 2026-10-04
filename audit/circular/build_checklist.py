#!/usr/bin/env python3
"""Classify the 191 lint hits (circular_candidates.csv) and emit
circular_candidates_classified.csv, CHECKLIST.md and allowlist.txt.

Category rules are keyed on the hypothesis definition; they were decided by
reading each definition and theorem (see README.md for the reasoning)."""
import csv
from collections import OrderedDict
from pathlib import Path

HERE = Path(__file__).resolve().parent
ORDER = ["Spt1", "Spt2", "Spt3", "Spt4", "Spt5", "Spt6", "Spt7", "Mock1", "Mock1_Advanced",
         "Mock2", "Mock2_Advanced", "Mock2_FunctionalAnalysis", "QYM"]

# A: circular / definitional tautology presented as a paper result -> must fix
A = {
    "SatisfiesHasse": "Hasse 한계 자체를 가정해 `ec_hasse`로 제시(독스트링은 조건부임을 명시). 래퍼 정리 삭제 또는 외부 입력으로만 남기고 원장 표기 수정.",
    "GoldwasserKilianPropagationTheorem": "GK 전파 정리를 가정. 게다가 `ECStepCertificate E X` 필드가 X를 제약하지 않아 진술이 거짓일 가능성(감사 보고 Spt1). 진술을 바로잡거나 삭제. 거짓 가설을 남기지 말 것.",
    "MtALogInput": "정의가 결론 `k ≤ v_p(Λ−u)` 그 자체(Remark 2.2로 표기). 파일의 `padicLog1p` 결과로 해소 시도, 불가하면 래퍼 삭제.",
    "AKSIsComplete": "`∀ X, X.Prime ↔ FEC X`를 가정해 `X.Prime ↔ FEC X`를 결론(Theorem 18로 표기). 삭제 또는 `_of_assumed_complete`로 개명하고 인증 목록·경계 레코드에서 제거.",
    "DirichletDensityAP": "디리클레 밀도 정리를 가정해 `thm836_part2`로 제시(독스트링은 조건부 명시). Mathlib로 해소 가능한지 확인, 불가하면 래퍼 삭제.",
    "goodReduction": "`goodReduction := ¬ p ∣ Δ`의 정의 동어반복을 'Claim 9.1 (necessary)'로 표기. `goodReduction_iff` 같은 정의 API로 개명하고 논문 라벨 제거.",
    "goodOpen": "`etalePiece := goodOpen`으로 정의해 놓고 étale 다리로 제시(정의 동어반복). 프록시 정의 제거 또는 '모델'로 명시.",
    "CoeffAgreement": "`CoeffAgreement p q := p = q`로 '계수 강성'을 제시(동어반복, 원장이 unconditional로 표기). 정의 삭제, 사용처를 `p = q`로 대체, 원장 수정.",
    "ModularCovarianceRestrictionStable": "추상 Lemma 6.1을 가정 그 자체로 제시. 기하판 `lemma6_1`(Mock2 17325, 실제 증명)로 대체하거나 삭제.",
}
# B: restatement destructors of bundled paper claims / certificate statements -> remove or isolate
B = {
    "gateECRegularData", "gateECRegularModelData",
    "WeightPurityGate", "EquivalenceCGate", "GlobalRiemannHypothesisGate",
    "UniformError",
}
B_PREFIXES = ("PaperInstancesHRlf", "AdvancedClaimsII")
# D: conditional but the hypothesis is proved in the same file
D = {
    "FiniteMahlerBinomialInversion": "Mock1 4826에서 해소됨. 가설 없는 무조건 따름정리 추가 권장.",
    "FiniteMahlerInterpolationUnique": "Mock1 4853에서 해소됨. 가설 없는 무조건 따름정리 추가 권장.",
    "GammaTwoThreeCuspCompactCofinal": "Mock2_FA 10532/10710에서 해소됨(`gammaTwoGeometricCompactCofinal_unconditional`). 무조건 따름정리 추가 권장.",
}
C_NOTES = {
    "FlatSector": "정의가 `QCurvature x = x`로 되어 있어 의도(=0?) 확인 필요.",
    "RealSmooth": "실제 보조정리를 쓰는 짧은 증명(탐지 오탐).",
    "HasQuotientCompactSupport": "실제 보조정리를 쓰는 짧은 증명(탐지 오탐).",
    "IsPlanarAffineWeakGraph": "보조정리 `friedrichs_identity` 경유(탐지 오탐).",
    "IsScalarQCyclic": "보조정리 `eq_zero_of_ne_one` 경유(탐지 오탐).",
    "IsSquareIntegrableOnActualStage": "Mathlib `coeFn_toLp` 경유(탐지 오탐).",
    "MassConditionAt": "한 단계 `trans_le` 유도(정상).",
    "IsPositiveCoerciveShift": "20766/23293에 같은 이름 분해 정리 중복 — 하나로 합칠 것.",
}


def category(t):
    if t in A:
        return "A", "FIX", A[t]
    if t in B or t.startswith(B_PREFIXES):
        note = ("논문 주장·인증서를 묶은 Prop의 분해/재진술. 내용 없음. 삭제하거나 API로 격리하고 증거로 세지 말 것."
                if t not in ("UniformError",) else
                "가설 `UniformError`가 논문 Thm 4.31의 결론(정직하게 가설로 표기). 분해 정리 자체는 무해하나 이를 소비하는 정리가 '증명'으로 집계되지 않게 할 것.")
        if t.startswith(B_PREFIXES):
            note = "퇴화 reference 객체에 대한 '논문 진술' 묶음의 분해(재진술 층). 삭제 또는 축소 권장."
        return "B", "REMOVE-OR-ISOLATE", note
    if t in D:
        return "D", "KEEP+UNCONDITIONAL-COROLLARY", D[t]
    return "C", "KEEP", C_NOTES.get(t, "실제 정의의 표준 분해(API) 보조정리. 유지.")


def main():
    rows = list(csv.DictReader((HERE / "circular_candidates.csv").open()))
    rows.sort(key=lambda r: (ORDER.index(r["module"]), int(r["line"])))
    out = []
    for i, r in enumerate(rows, 1):
        cat, action, note = category(r["hyp_type"])
        r = OrderedDict(id=f"C{i:03d}", category=cat, action=action, note=note, **r)
        out.append(r)
    with (HERE / "circular_candidates_classified.csv").open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=list(out[0].keys()))
        w.writeheader()
        w.writerows(out)
    allow = ["# C (정상 API/오탐) 및 D (같은 파일에서 해소) 항목: 린트 플래그에서 제외",
             "# Codex가 B 항목을 API로 격리하기로 결정한 경우에만 사유와 함께 추가"]
    allow += [f"{r['module']}:{r['theorem']}" for r in out if r["category"] in ("C", "D")]
    (HERE / "allowlist.txt").write_text("\n".join(allow) + "\n")
    counts = {c: sum(r["category"] == c for r in out) for c in "ABCD"}
    lines = ["# 순환 후보 체크리스트 (자동 탐지 191개)", "",
             f"분류: A {counts['A']} (수정 필수) · B {counts['B']} (삭제/격리) · C {counts['C']} (유지) · D {counts['D']} (유지+무조건 따름정리)",
             "", "처리 후 각 줄을 `- [x] … — 결과: FIXED/DELETED/ISOLATED/KEPT (방법)` 형식으로 갱신하세요.", ""]
    for cat, title in [("A", "A. 순환·동어반복 — 수정 필수"), ("B", "B. 재진술 분해 — 삭제 또는 격리"),
                       ("D", "D. 조건부이나 해소됨 — 유지 + 무조건 따름정리"), ("C", "C. 정상 API / 탐지 오탐 — 유지(확인만)")]:
        lines += [f"## {title}", ""]
        for r in out:
            if r["category"] != cat:
                continue
            lines.append(f"- [ ] **{r['id']}** `{r['module']}.lean:{r['line']}` `{r['theorem']}` := `{r['proof'][:90]}` "
                         f"— 가설 `{r['hyp_type']}` ({r['def_module']}:{r['def_line']}) — {r['note']}")
        lines.append("")
    (HERE / "CHECKLIST.md").write_text("\n".join(lines))
    print(counts)


if __name__ == "__main__":
    main()
