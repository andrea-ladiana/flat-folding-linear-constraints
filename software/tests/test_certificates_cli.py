"""Certificates (round trip, tampering), export and the command line."""

import copy
import io
import itertools
import json
import os

import pytest

from linfold import analyze, from_segments, load, verify
from linfold import generators as gen
from linfold.cli import main
from linfold.export import system_dict, write_xnf
from helpers import EXAMPLES


def ex(name):
    return os.path.join(EXAMPLES, name)


@pytest.fixture(scope="module")
def triangle_doc():
    cp = load(ex("triangle.fold"))
    rep = analyze(cp)
    return rep.certificate.to_json(cp, source=ex("triangle.fold")), cp


def test_certificate_round_trip(triangle_doc):
    doc, cp = triangle_doc
    doc = json.loads(json.dumps(doc))
    res = verify(doc, cp)
    assert res.algebra and res.geometry, res.messages
    assert verify(doc).ok


def test_tampered_certificates_fail(triangle_doc):
    doc, cp = triangle_doc
    bad = copy.deepcopy(doc)
    del bad["items"][0]                                 # no longer sums to 0 = 1
    assert not verify(bad).algebra
    bad = copy.deepcopy(doc)
    bad["items"][0]["terms"][0].reverse()               # a false equation
    bad["items"][0]["equation"]["rhs"] ^= 1
    bad["items"][1]["terms"][0].reverse()
    bad["items"][1]["equation"]["rhs"] ^= 1
    res = verify(bad, cp)
    assert res.algebra and res.geometry is False


def test_label_certificate_round_trip():
    cp = load(ex("vertex_degree16_wrong_labels.fold"))
    rep = analyze(cp)
    doc = json.loads(json.dumps(rep.certificate.to_json(cp)))
    assert verify(doc, cp).ok
    bad = copy.deepcopy(doc)
    k = next(i for i, d in enumerate(bad["items"]) if d["kind"] == "assignment")
    bad["items"][k]["label"] = "M" if bad["items"][k]["label"] == "V" else "V"
    bad["items"][k]["equation"]["rhs"] ^= 1
    assert not verify(bad).algebra


def _count_xnf(text, nvars):
    xor, cls = [], []
    for line in text.splitlines():
        if not line or line[0] in "cp":
            continue
        if line.startswith("x"):
            xor.append([int(t) for t in line[1:].split()[:-1]])
        else:
            cls.append([int(t) for t in line.split()[:-1]])
    n = 0
    for bitsv in itertools.product((0, 1), repeat=nvars):
        val = lambda l: bitsv[abs(l) - 1] ^ (l < 0)      # noqa: E731
        if all(sum(val(l) for l in c) % 2 == 1 for c in xor) and \
                all(any(val(l) for l in c) for c in cls):
            n += 1
    return n


@pytest.mark.parametrize("angles,states", [([40, 70, 100, 60, 40, 50], 12),
                                           ([60, 100, 120, 80], 4)])
def test_xnf_counts_flat_folded_states(angles, states):
    cp = from_segments(gen.single_vertex(angles), "v")
    buf = io.StringIO()
    counts = write_xnf(cp, buf)
    assert _count_xnf(buf.getvalue(), counts["variables"]) == states


def test_system_dict():
    cp = load(ex("map_3x3.fold"))
    d = system_dict(cp)
    assert len(d["variables"]) == 36 and len(d["rows"]) == 12
    assert d["transitivity"]["complete"]


def test_cli_vertex(capsys):
    assert main(["vertex", "40", "70", "100", "60", "40", "50", "--mv", "MMMMVV"]) == 0
    out = capsys.readouterr().out
    assert "e2, e3: equal" in out and "flat-foldable (Hull): yes" in out
    assert main(["vertex", "45", "135", "135", "45", "--mv", "VMVV"]) == 2
    assert main(["vertex", "90", "90", "100"]) == 1
    capsys.readouterr()
    assert main(["vertex", "10", "30", "50", "30", "--cone", "--json"]) == 0
    json.loads(capsys.readouterr().out)


def test_cli_check_verify_export(tmp_path, capsys):
    cert = tmp_path / "c.json"
    svg = tmp_path / "t.svg"
    assert main(["check", ex("triangle.fold"), "--certificate", str(cert),
                 "--svg", str(svg)]) == 2
    assert "NOT FLAT-FOLDABLE" in capsys.readouterr().out
    assert svg.read_text(encoding="utf-8").startswith("<svg")
    assert main(["verify", str(cert), "--pattern", ex("triangle.fold")]) == 0
    assert "VALID" in capsys.readouterr().out
    assert main(["check", ex("miura_6x6.fold"), "--format", "json"]) == 0
    rep = json.loads(capsys.readouterr().out)
    assert rep["verdict"] == "passes" and rep["global"]["consistent"]
    assert main(["check", ex("vertex_example1.fold"), "--format", "markdown"]) == 0
    out = tmp_path / "s.cnf"
    assert main(["export", ex("vertex_example1.fold"), "-o", str(out), "--format", "xnf"]) == 0
    assert main(["check", ex("nonexistent.fold")]) == 1


def test_cli_complete(tmp_path, capsys):
    segs = gen.single_vertex([60, 100, 120, 80], "MUUU")
    from linfold.generators import write_segments
    src = tmp_path / "v.fold"
    write_segments(str(src), segs)
    out = tmp_path / "done.fold"
    assert main(["check", str(src), "--complete", str(out)]) == 0
    doc = json.loads(out.read_text(encoding="utf-8"))
    assert doc["edges_assignment"].count("V") == 1
