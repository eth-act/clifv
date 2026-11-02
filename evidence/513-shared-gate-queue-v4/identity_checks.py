"""Check retained compilation stages independently from exact-byte matches."""
COMPILED = {'identical_code_artifact', 'different_code_artifact'}
def require_production_compiled(prior, current):
    accepted = {key for key,row in prior.items() if row['status'] in COMPILED}
    lost = sorted(key for key in accepted if key not in current or current[key]['status'] not in COMPILED)
    assert not lost, ('Previously compiled production identities regressed',lost)
    return {'prior_compiled_identities':len(accepted),'compiled_retained':len(accepted),'compiled_stage_losses':lost}
