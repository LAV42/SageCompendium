from sage.interfaces.singular import singular
singular.lib('nctools.lib')


def superspace(N, parameters=['q', 't', 'alpha'], alphabet=None):
    """Define a superspace in 2*N+1 variables using singular."""
    if alphabet is None:
        names = (
            ['dtheta'] +
            ['theta_'+str(k) for k in range(N)] +
            ['x_'+str(k) for k in range(N)]
        )
    else:
        print('Custom alphabet not yet implemented.')
        return None
    name_str = '(' + ','.join(names) + ')'
    coeff_ring_str = '(0,' + ','.join(parameters) + ')'
    R = singular.ring(coeff_ring_str, name_str, 'lp')
    singular.setring(R)
    ER = singular.superCommutative(1, N+1)
    singular.setring(ER)
    # print(ER)
    for a_name in names:
        globals()[a_name] = singular(a_name)
    globals()['singular_vars'] = names
    globals()['dummy_odd'] = singular('dtheta')
    return ER


def sDiff(expr, var, dtheta=None):
    if dtheta is None:
        dtheta = globals()['dummy_odd']
    new_expr = singular.substitute(expr, var, dtheta)
    new_expr = singular.diff(new_expr, dtheta)
    return new_expr


def is_symmetric():
    pass


def var_to_monomials():
    pass


def mono_expand(N, conditions = None):
    pass
