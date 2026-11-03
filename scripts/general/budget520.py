"""Exact numerical IOP budget for the actual frozen general-circuit dimensions."""
from fractions import Fraction as F
import math


def evaluate(p):
    q=1<<256
    assert p['d']==256 and p['nu']==10
    r,exc=p['expected_challenge_stages'],p['excluded_raw_coordinates']
    assert r<=65536 and exc<=65536 and max(p['row_bits'],p['column_bits'])<=64
    rank=sum((F(1+((1<<(1<<i))-1)**2,q) for i in range(6)),F(0))
    rank+=F(1,q)+F(((1<<64)-1)**2,q*((1<<24)-1))+F(1,1<<164)
    endpoint=4*rank+F(3*(p['row_bits']-10)+p['column_bits']-10,q)
    local=[F(p['row_bits'],q),F(3,q)]
    coverage=F(0)
    for t in p['private_setups']:
        ell,c,gamma=t['ell'],t['cstar'],t['gamma']
        assert 11<=ell<=40 and t['n1']<=1<<64 and gamma==520 and t['tau']==4 and t['beta']==2
        local.extend([F(8,q),(F(t['n1'])*F(1249,10000)+3)/(q-1),F(8751,10000)**gamma])
        dpre=2*ell*ell-3*ell+2
        djoint=gamma*c*(c-1)//2+c*(1<<(ell-c))+2*c*(c+1)
        coverage+=F(dpre+djoint,q-1)
    for t in p['public_indices']:
        assert t['S_plus_B']<=1<<64 and t['largest_n1']<=1<<64
        local.extend([F(5,q),F(4*t['S_plus_B'],q),(F(t['largest_n1'],5)+3)/(q-1),F(4,5)**520])
    if 'public_columns' in p:
        t=p['public_columns']
        assert t['log']==p['row_bits']+3 and t['batch_size']==6 and t['queries']==520
        assert t['largest_n1']==2<<t['log'] and t['largest_n1']<=1<<64
        # Six fixed claims use independent uniform coefficients: a nonzero error vector
        # has one hyperplane of cancelling coefficients, with probability exactly 1/q.
        local.extend([F(1,q),(F(t['largest_n1'],5)+3)/(q-1),F(4,5)**520])
    if 'onehot_index' in p:
        t=p['onehot_index']
        assert t['block_bits'] in [3,5] and t['blocks']==(p['row_bits']+p['column_bits']+t['block_bits']-1)//t['block_bits']
        assert t['outer_degree']==t['blocks']+1 and t['selector_bits']==(t['blocks']-1).bit_length()
        assert t['gamma']==520 and t['tau']==4 and t['beta']==2 and 11<=t['ell']<=40 and t['n1']<=1<<64
        # Conservative whole outer/reduction error, included as one local term;
        # the final R*max(local) remains a union bound. Index contains public bits,
        # so it adds knowledge error and challenges, not private mask leakage.
        local.extend([F(t['entry_bits']*t['outer_degree']+1+2*(t['block_bits']+t['selector_bits']),q),
            F(8,q),(F(t['n1'])*F(1249,10000)+3)/(q-1),F(8751,10000)**520])
    knowledge=r*max(local)
    zk=2*(endpoint+F(exc,q)+coverage)
    assert max(local)<F(1,1<<100) and zk<F(1,1<<100)
    return {'scope':'approx100-bit per-round convention; accumulated interactive value separate; not final Fiat-Shamir certificate','gamma':520,'delta_private':'1249/10000','delta_public':'1/5','per_round_error_upper_bound':str(max(local)),'per_round_bits_lower_bound':-math.log2(float(max(local))),
            'knowledge_error_upper_bound':str(knowledge),'zk_error_upper_bound':str(zk),
            'knowledge_bits_lower_bound':-math.log2(float(knowledge)),
            'zk_bits_lower_bound':-math.log2(float(zk)),
            'raw_exclusion_count':exc,'challenge_stages':r}
