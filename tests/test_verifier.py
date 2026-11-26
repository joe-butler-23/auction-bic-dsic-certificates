"""
Verifier Integrity & Forgery-Rejection Test Suite for `verify_all_certificates.py`
==================================================================================
Mutates copies of the real certificates in a temporary directory across 22 concrete
corruption/forgery classes (covering DSIC RT_0 .npz, BIC polygon menus, explicit
ex-post priority-tier .json tables, and SHA256SUMS) and verifies 100% rejection
under `python3 -O`.
"""

import json
from pathlib import Path
import shutil
import sys
import tempfile
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
import verify_all_certificates as V


def expect_reject(name: str, fn) -> None:
    try:
        fn()
    except ValueError as exc:
        print(f"  [REJECTED OK] {name}: {exc}")
        return
    raise RuntimeError(f"FORGERY ACCEPTED BY VERIFIER: {name}")


def mutate_npz(src: Path, dst: Path, mutator) -> Path:
    with np.load(src, allow_pickle=False) as d:
        data = {k: d[k].copy() for k in d.files}
    mutator(data)
    np.savez(dst, **data)
    return dst


def mutate_json(src: Path, dst: Path, mutator) -> Path:
    data = json.loads(src.read_text(encoding="utf-8"))
    mutator(data)
    dst.write_text(json.dumps(data, separators=(",", ":")), encoding="utf-8")
    return dst


def main() -> None:
    cdir = ROOT / "certificates"
    with tempfile.TemporaryDirectory() as td:
        tdir = Path(td)

        # F1: 2x2 DSIC — violate cell divergence
        def m_f1(d):
            d["F_int"][0, 0, 1, 0] += int(d["denom"]) * 3 + 1
        p = mutate_npz(cdir / "exact_cert_dsic_b2_m10.npz", tdir / "f1.npz", m_f1)
        expect_reject("F1_2x2_div_violation", lambda: V.verify_dsic_2x2_u01(p, quiet=True))

        # F2: 2x2 DSIC — violate lower boundary F[..., 0, j] > 0
        def m_f2(d):
            d["F_int"][0, 0, 0, 0] = 1
        p = mutate_npz(cdir / "exact_cert_dsic_b2_m10.npz", tdir / "f2.npz", m_f2)
        expect_reject("F2_2x2_b0_violation", lambda: V.verify_dsic_2x2_u01(p, quiet=True))

        # F3: 2x2 DSIC — violate upper boundary F[..., M, j] < 1
        def m_f3(d):
            M = int(d["M"])
            d["F_int"][0, 0, M, 0] = int(d["denom"]) - 1
        p = mutate_npz(cdir / "exact_cert_dsic_b2_m10.npz", tdir / "f3.npz", m_f3)
        expect_reject("F3_2x2_b1_violation", lambda: V.verify_dsic_2x2_u01(p, quiet=True))

        # F4: 2x2 DSIC — float64 dtype smuggling in F_int
        def m_f4(d):
            d["F_int"] = d["F_int"].astype(np.float64)
        p = mutate_npz(cdir / "exact_cert_dsic_b2_m10.npz", tdir / "f4.npz", m_f4)
        expect_reject("F4_2x2_float_dtype_smuggling", lambda: V.verify_dsic_2x2_u01(p, quiet=True))

        # F5: 2x2 DSIC — non-positive denom
        def m_f5(d):
            d["denom"] = np.int64(0)
        p = mutate_npz(cdir / "exact_cert_dsic_b2_m10.npz", tdir / "f5.npz", m_f5)
        expect_reject("F5_2x2_zero_denom", lambda: V.verify_dsic_2x2_u01(p, quiet=True))

        # F6: 3x2 DSIC — violate divergence
        def m_f6(d):
            d["F_int"][0, 1, 0] += int(d["denom"]) * 3 + 1
        p = mutate_npz(cdir / "exact_cert_dsic_b3_m5.npz", tdir / "f6.npz", m_f6)
        expect_reject("F6_3x2_div_violation", lambda: V.verify_dsic_3x2_u01(p, quiet=True))

        # F7: 3x2 DSIC — wrong shape
        def m_f7(d):
            d["F_int"] = d["F_int"][:-1]
        p = mutate_npz(cdir / "exact_cert_dsic_b3_m5.npz", tdir / "f7.npz", m_f7)
        expect_reject("F7_3x2_wrong_shape", lambda: V.verify_dsic_3x2_u01(p, quiet=True))

        # F8: Beta(1,2) — violate lower boundary W[k,l,0,j]*M <= D*(M-j-1)
        def m_f8(d):
            M = int(d["M"])
            d["W_int"][0, 0, 0, M - 1] = 1
        p = mutate_npz(cdir / "exact_cert_dsic_beta12_m8.npz", tdir / "f8.npz", m_f8)
        expect_reject("F8_beta12_b0_violation", lambda: V.verify_dsic_2x2_beta12(p, S=2, quiet=True))

        # F9: Beta(1,2) — violate residual divergence <= 0
        def m_f9(d):
            d["W_int"][0, 0, 1, 0] = int(d["W_int"][0, 0, 0, 0]) + 1
        p = mutate_npz(cdir / "exact_cert_dsic_beta12_m8.npz", tdir / "f9.npz", m_f9)
        expect_reject("F9_beta12_div_violation", lambda: V.verify_dsic_2x2_beta12(p, S=2, quiet=True))

        # F10: 6D 2x3 — break (23) item-stabilizer equivariance
        def m_f10(d):
            M = int(d["M"])
            arr6 = d["F_int"].reshape((M, M, M, M + 1, M, M))
            arr6[0, 1, 2, 1, 0, 1] += 1
            d["F_int"] = arr6.reshape(d["F_int"].shape)
        p = mutate_npz(cdir / "exact_cert_dsic_2x3_m4.npz", tdir / "f10.npz", m_f10)
        expect_reject("F10_2x3_symmetry_break", lambda: V.verify_dsic_2x3_u01(p, require_s3_equivariance=True, quiet=True))

        # F11: 6D 2x3 — violate 3D divergence <= 4/M
        def m_f11(d):
            M = int(d["M"])
            arr6 = d["F_int"].reshape((M, M, M, M + 1, M, M))
            arr6[0, 0, 0, 1, 0, 0] += int(d["denom"]) * 4 + 1
            d["F_int"] = arr6.reshape(d["F_int"].shape)
        p = mutate_npz(cdir / "exact_cert_dsic_2x3_m4.npz", tdir / "f11.npz", m_f11)
        expect_reject("F11_2x3_div_violation", lambda: V.verify_dsic_2x3_u01(p, require_s3_equivariance=True, quiet=True))

        # F12: BIC menu — missing outside option (0,0,0)
        def m_f12(d):
            mask = ~((d["a_int"] == 0) & (d["b_int"] == 0) & (d["p_int"] == 0))
            d["a_int"], d["b_int"], d["p_int"] = d["a_int"][mask], d["b_int"][mask], d["p_int"][mask]
        p = mutate_npz(cdir / "cert_bic_b3_n24.npz", tdir / "f12.npz", m_f12)
        expect_reject("F12_bic_missing_zero_option", lambda: V.verify_bic_u01(p, expected_B=3, quiet=True))

        # F13: BIC menu — out-of-range allocation (> denom)
        def m_f13(d):
            d["a_int"][0] = int(d["denom"]) + 1
        p = mutate_npz(cdir / "cert_bic_b3_n24.npz", tdir / "f13.npz", m_f13)
        expect_reject("F13_bic_alloc_gt_1", lambda: V.verify_bic_u01(p, expected_B=3, quiet=True))

        # F14: Pinned SHA256SUMS tamper check
        cdir_copy = tdir / "certs_copy"
        shutil.copytree(cdir, cdir_copy)
        sums = (cdir_copy / "SHA256SUMS").read_text()
        tampered = ("0" if sums[0] != "0" else "1") + sums[1:]
        (cdir_copy / "SHA256SUMS").write_text(tampered)
        expect_reject("F14_sha256_manifest_tamper", lambda: V.verify_pinned_hashes(cdir_copy))

        # Use the faster B=3 menu for F15..F22 explicit ex-post JSON tests
        b3_menu = cdir / "cert_bic_b3_n24.npz"
        b3_expost = cdir / "cert_expost_bic_b3.json"

        # F15: Ex-post BIC — negative probability numerator
        def m_f15(d):
            d["entries"][0][2] = -1
        pj = mutate_json(b3_expost, tdir / "f15.json", m_f15)
        expect_reject("F15_expost_negative_prob", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F16: Ex-post BIC — broken row sum (P_{r,m} incremented by +1)
        def m_f16(d):
            d["entries"][0][2] += 1
        pj = mutate_json(b3_expost, tdir / "f16.json", m_f16)
        expect_reject("F16_expost_row_sum_mismatch", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F17: Ex-post BIC — broken column mass balance (U_edges_num perturbed)
        def m_f17(d):
            d["U_edges_num"][1] += 1
        pj = mutate_json(b3_expost, tdir / "f17.json", m_f17)
        expect_reject("F17_expost_col_mass_mismatch", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F18: Ex-post BIC — broken marginal expectation (rho_num lowered)
        def m_f18(d):
            d["rho_num"] -= 1
        pj = mutate_json(b3_expost, tdir / "f18.json", m_f18)
        expect_reject("F18_expost_marginal_mismatch", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F19: Ex-post BIC — U_edges_num[M] > U_denom (invalid total mass > 1)
        def m_f19(d):
            d["U_edges_num"][-1] = d["U_denom"] + 1
        pj = mutate_json(b3_expost, tdir / "f19.json", m_f19)
        expect_reject("F19_expost_mass_gt_1", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F20: Ex-post BIC — float/bool smuggling in integer field
        def m_f20(d):
            d["M"] = True
        pj = mutate_json(b3_expost, tdir / "f20.json", m_f20)
        expect_reject("F20_expost_bool_int_smuggling", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

        # F21: Ex-post BIC — duplicate JSON key injection
        raw = b3_expost.read_text(encoding="utf-8")
        dup_path = tdir / "f21.json"
        dup_path.write_text('{"B":3,' + raw[1:], encoding="utf-8")
        expect_reject("F21_expost_duplicate_json_key", lambda: V.verify_expost_bic_u01(b3_menu, dup_path, expected_B=3, quiet=True))

        # F22: Ex-post BIC — duplicate (r, m) sparse entry injection
        def m_f22(d):
            d["entries"].append(list(d["entries"][0]))
        pj = mutate_json(b3_expost, tdir / "f22.json", m_f22)
        expect_reject("F22_expost_duplicate_rm_entry", lambda: V.verify_expost_bic_u01(b3_menu, pj, expected_B=3, quiet=True))

    print("ALL 22/22 FORGERY TESTS REJECTED (python3 -O SAFE).")


if __name__ == "__main__":
    main()
