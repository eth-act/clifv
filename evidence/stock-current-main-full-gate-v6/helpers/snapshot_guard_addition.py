def snapshot_blob(path):
    data = os.readlink(path).encode() if path.is_symlink() else path.read_bytes()
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


def verify_snapshot_files(view, blobs, operational):
    allowed = {"lakefile.toml"}
    assert set(operational) <= allowed, "Unexpected operational source exception"
    for relative, expected in blobs.items():
        path = view / relative
        if relative in operational:
            item = operational[relative]
            assert item["canonical_blob"] == expected, relative
            assert sha(path) == item["sha256"], ("Operational source changed", relative)
        else:
            assert snapshot_blob(path) == expected, ("Snapshot source changed", relative)


def snapshot_revision(view, manifest_path):
    manifest_path = manifest_path.resolve()
    manifest = json.loads(manifest_path.read_text())
    assert Path(manifest["view"]).resolve() == view
    assert Path(manifest["execution_harness"]["path"]).resolve() == Path(__file__).resolve()
    assert sha(Path(__file__).resolve()) == manifest["execution_harness"]["sha256"]
    repository = Path(manifest["source_repository"]).resolve()
    revision = manifest["revision"]
    tree = subprocess.check_output(["git", "rev-parse", revision + "^{tree}"], cwd=repository, text=True).strip()
    assert tree == manifest["tree"], "Snapshot revision/tree mismatch"
    entries = subprocess.check_output(["git", "ls-tree", "-rz", tree], cwd=repository)
    blobs = {}
    for entry in entries.split(b"\0"):
        if not entry:
            continue
        header, name = entry.split(b"\t", 1)
        mode, kind, value = header.decode().split()
        if kind == "blob":
            blobs[name.decode()] = value
    assert blobs == manifest["source_blobs"], "Snapshot inventory differs from the exact repository tree"
    verify_snapshot_files(view, blobs, manifest["operational_sources"])
    # Only the build job limit can differ in the Lake configuration.
    canonical = subprocess.check_output(["git", "cat-file", "blob", blobs["lakefile.toml"]], cwd=repository)
    assert (view / "lakefile.toml").read_bytes() == canonical.replace(b"weakLeanArgs = [", b'weakLeanArgs = ["-j2",', 1)
    expected = {name for name in blobs if name.endswith(".lean") and name.startswith(("FV/", "FVTest/"))}
    actual = {str(path.relative_to(view)) for folder in ("FV", "FVTest") for path in (view / folder).rglob("*.lean")}
    assert actual == expected, "Unreviewed or missing Lean source"
    return revision, {"manifest": str(manifest_path), "manifest_sha256": sha(manifest_path), "tree": tree,
                      "operational_sources": manifest["operational_sources"]}
