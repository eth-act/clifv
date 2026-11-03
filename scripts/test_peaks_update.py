import importlib.util, pathlib, tempfile, unittest

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("peaks_update", HERE / "peaks-update.py")
pu = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pu)


class PeaksUpdate(unittest.TestCase):
    def test_drift_and_write(self):
        with tempfile.TemporaryDirectory() as t:
            t = pathlib.Path(t)
            table = t / "peaks.tsv"
            table.write_text("# header\nA\t1000\t62\nB\t8000\t100\nC\t2000\t300\n")
            sched = t / "sched"
            sched.mkdir()
            # A got much slower (the RuleArith5 case), B needs far more memory than recorded,
            # C is within noise, D has no record; E was only restored, not built
            (sched / "sched.log").write_text(
                "10:00:00 done A rc=0 912s maxrss=1.0G cgpeak=0.2G built -> ok\n"
                "10:00:00 done B rc=0 200s maxrss=20.0G cgpeak=19G built -> ok\n"
                "10:00:00 done C rc=0 700s maxrss=2.0G cgpeak=1G built -> ok\n"
                "10:00:00 done D rc=0 40s maxrss=3.0G cgpeak=1G built -> ok\n"
                "10:00:00 done E rc=0 1s maxrss=0.1G cgpeak=0.1G up-to-date -> ok\n")
            (sched / "B.time").write_text("Maximum resident set size (kbytes): 20971520\n")
            header, rows = pu.read_table(table)
            # CI units: seconds measured at time scale 2 (A: 912 s -> 456 s recorded)
            measured = {m: (mb, s / 2) for m, (mb, s) in pu.read_sched(sched).items()}
            kinds = {(k, m) for k, m, _, _ in pu.drift(rows, measured)}
            self.assertEqual(kinds, {("slower", "A"), ("memory", "B"), ("new", "D")})


if __name__ == "__main__":
    unittest.main()
