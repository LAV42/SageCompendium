"""Allows the manipulation of superpolynomials in variables."""
from sage.interfaces.singular import singular
from superpartition import _Superpartitions
from sage.rings.rational_field import QQ
from sage.groups.perm_gps.permgroup_named import SymmetricGroup
from sage.functions.other import factorial
from sym_superfunct import unique_perm_list_elements
from sage.misc.misc_c import prod
from functools import reduce
import operator
singular.lib('nctools.lib')


class superspace:
    """General class for functions on variables in superspace."""

    def __init__(self, N, parameters=['q', 't', 'alpha']):
        """Define a superspace in 2*N+1 variables using singular."""
        r"""
            The +1 in the number of variables is due to a Dummy fermionic
            variable that we introduce so that differentiation works.
            The variables are x_i, theta_i for 0<= i < N.
        """
        x_var = ['x_'+str(k) for k in range(N)]
        theta_var = ['theta_'+str(k) for k in range(N)]
        names = (['dtheta'] + theta_var + x_var)

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

        self._N = N
        self._SN = SymmetricGroup(range(N))
        self._param_names = parameters
        self._base_ring = ER
        self._x_var = x_var
        self._theta_var = theta_var

    def __repr__(self):
        """Give basic informations about ring."""
        out = ("Superspace in 2*" + str(self._N) + " variables." +
               " With alphabet theta_0 ... theta_N-1, x_0 ... x_N-1.")
        return out

    def SN(self):
        """Return the class instance of the symmetric group."""
        return self._SN

    def x_vars(self):
        """Return a list of the x variables."""
        return [singular(x) for x in self._x_var]

    def theta_vars(self):
        """Return a list of the theta variables."""
        return [singular(theta) for theta in self._theta_var]

    def diff(self, expr, var, dtheta=None):
        """Differentiate in superspace."""
        r"""
            This is a work around since the differentiation in superspace is
            not implemented in singular. It works fine though, but this
            workaround makes it so that one cannot use robustely his own
            alphabet.

            The idea is that the dummy indices is the first in the
            lexicographic order, so if we want to differentiate with respect to
            theta_3 for instance, substituting theta_3 for the dummy variable
            will bring it all the way upfront of the monomial hence producing
            the right sign. Then differentiation will simply remove the dummy
            variable and the resulting in the right expression.
        """
        if var*var == 0:
            if dtheta is None:
                dtheta = globals()['dummy_odd']
            new_expr = singular.substitute(expr, var, dtheta)
            new_expr = singular.diff(new_expr, dtheta)
        else:
            new_expr = singular.diff(expr, var)
        return new_expr

    def theta_project(self, expr):
        """Return the coefficient of theta_0..theta_{m-1}."""
        _, fermionic_sect = self.get_sector(expr)
        theta_monomial = prod(self.theta_vars()[:fermionic_sect])
        expr = expr.coef(theta_monomial)[1][2]
        return expr

    def vandermonde(self, fermionic_sector):
        """Return the Vandermonde of fermionic_sector variables."""
        X = self.x_vars()
        xij = [X[i] - X[j]
               for j in range(fermionic_sector)
               for i in range(j)]
        delta_m = prod(xij)
        return delta_m

    def get_sector(self, expr):
        """Given an expression, return the sector to which it belongs."""
        vec = expr.leadexp().sage()
        N = self._N
        fermionic_degree = sum(vec[:N+1])
        bosonic_degree = sum(vec[N+1:])
        return (bosonic_degree, fermionic_degree)

    def _int_vec_is_ordered(self, intvec):
        """Check wether the intvec taken from a supermonomial is a spart."""
        N = self._N
        thetas = intvec[1:N+1]
        x_var = intvec[N+1:]

        is_sorted = False

        fermionic_part = [part
                          for (part, ferm) in zip(x_var, thetas)
                          if ferm]
        if sorted(fermionic_part, reverse=True) == fermionic_part:
            is_sorted = True
        # Make sure we exit as soon as we know since this is going to be
        # called quite a lot
        if not is_sorted:
            return False
        bosonic_part = [part
                        for (part, ferm) in zip(x_var, thetas)
                        if not ferm]
        # Here we keep the extra 0's because [4,2,0,1] is not ordered
        # but [4,2,1,0] is.
        if sorted(bosonic_part, reverse=True) == bosonic_part:
            # We don't have to `and` with previous result because
            # at this point is_sorted can't be False
            is_sorted = True
        else:
            is_sorted = False

        return is_sorted

    def _int_vec_to_spart(self, intvec):
        """Give the spart associated to the degree of a supermonomial."""
        """
            The intvec must be 2*N+1 dimensional, that is, it must
            include the Dummy fermionic variable index.
        """
        N = self._N

        # Retrieve which theta variables are present
        thetas = intvec[1:N+1]
        # Retrieve the x variables
        x_var = intvec[N+1:]

        # Fermionic parts are those which pair theta's and  x's of same index
        fermionic_part = [part
                          for (part, ferm) in zip(x_var, thetas)
                          if ferm]
        fermionic_part.sort(reverse=True)
        # Bosonic parts are the oposite
        bosonic_part = [part
                        for (part, ferm) in zip(x_var, thetas)
                        if not ferm]
        bosonic_part.sort(reverse=True)
        bosonic_part = [value for value in bosonic_part if value != 0]

        spart = _Superpartitions([fermionic_part, bosonic_part])
        return spart

    def ns_monomial(self, composition):
        """Return the monomial associated to composition."""
        N = self._N
        if len(composition) < N:
            composition = composition + [0
                                         for k in range(N - len(composition))]
        elif len(composition) > N:
            print('Composition too long')
            return 0
        x_var = self._x_var
        mono_str = '^%d*'.join(x_var) + '^%d'
        mono_str = mono_str % tuple(composition)
        mono = singular(mono_str)
        return mono

    def is_symmetric(self, expr):
        """Check if expr is symmetric in the current superspace."""
        N = self._N
        SN = self._SN
        Theta = self._theta_var
        X = self._x_var
        permutations = SN
        # We generate the permutations of the list of variables
        # Here we take permutations of length 1 since f is symmetric
        # if f = K_ij f for all ij.
        permVars = [['dtheta'] + permutation(Theta) + permutation(X)
                    for permutation in permutations
                    if permutation.length() == 1]
        # join everything as a big string
        maps_arg = [','.join(new_vars) for new_vars in permVars]
        # Dimensions for the future Singular matrix
        matrix_dim = (len(permVars), 2*N+1)
        # Code needed for the Matrix declaration
        # MM[i][j] where each row is a new permuation and j are the
        # theta_0, theta_1, ....
        matrix_declaration = ('matrix MM'+'[%d][%d]' % matrix_dim +
                              '=' + ','.join(maps_arg) + ';')
        singular.eval(matrix_declaration)
        # We define a variable to act as a Singular-Sage bridge
        out = singular.int(1)
        # We find out how Singular calls 'out' internaly
        singular_out = out.name()
        # We retrieve the Singular name of expr in the current session
        # so that we can call it from inside
        singular_expr = singular(expr).name()
        # Here we prepare what is going to be sent to Singular
        computemap = (
            # We set result to be true by default
            "int out = 1;"
            # This 'for' will loop over the rows of the Matrix
            # that is over every permutation of S_N
            "for(int i=1; i<=" + str(matrix_dim[0]) + "; i++){"
            # We define a map which will be the exchange operator
            "map f = basering, MM[i,1.." + str(matrix_dim[1]) + "];"
            # We apply the map and add the result to previous permutations
            "if(" + singular_expr + "!= f(" + singular_expr + ")){"
            "out = 0; break;};"
            "};" +
            # We define the 'out' known by Sage to be the Singular 'out'
            # This will update the value of out in Sage.
            singular_out + "= out;"
            "kill out;"
        )
        # We send all of this to singular
        singular.eval(computemap)
        return bool(out)

    def apply_permuation(self, expr, permutation):
        """Apply to expr a permutation of variables."""
        Theta = self._theta_var
        X = self._x_var
        KwTheta = permutation(Theta)
        KwX = permutation(X)
        new_vars = ['dtheta'] + KwTheta + KwX
        perm_string = ','.join(new_vars)
        sing_map = singular('basering,'+perm_string, type='map')
        new_expr = sing_map(expr)
        return new_expr

    # This method is fine but really sub-optimal.
    def symmetrize(self, expr, condition=None, normalize=None):
        """Symmetrize (in superspace) a Singular expression."""
        r"""
            Note that calling superspace.apply_permuation(expr) multiple times
            is not an option here since it is too slow. This function is fast
            because we send everything Singular needs to compute the result in
            a few operations only. Some operations are left in sage for the
            programmer convinience, but the idea is that we send all the
            permutations, (in maps_arg), as a Singular Matrix once which limits
            the number of times Sage has to give statements to Singular, this
            is typically the biggest bottleneck. The reason is that Sage
            is kind of typing everything in a internal singular_console().

            Note that this is very slow for a large number of variables.
            Because it is not obvious how to generate elements of S_N such that
            each permutation yields an unique result. So we compute
            non-distinct permutations. For instance, symmetrizing x_1^3 for N=4
            will yield a coefficient of 3!.

            This is why this method is not used for monomial computation.
        """
        N = self._N
        SN = self._SN
        Theta = self._theta_var
        X = self._x_var
        permutations = SN
        # We generate the permutations of the list of variables
        permVars = [['dtheta'] + permutation(Theta) + permutation(X)
                    for permutation in permutations]
        # join everything as a big string
        number_of_maps = len(permVars)
        maps_arg = [','.join(new_vars) for new_vars in permVars]
        # Dimensions for the future Singular matrix
        matrix_dim = (number_of_maps, 2*N+1)
        # Code needed for the Matrix declaration
        # MM[i][j] where each row is a new permuation and j are the
        # theta_0, theta_1, ....
        matrix_declaration = ('matrix MM'+'[%d][%d]' % matrix_dim +
                              '=' + ','.join(maps_arg) + ';')
        singular.eval(matrix_declaration)
        # We define a variable to act as a Singular-Sage bridge
        out = singular.poly(0)
        # We find out how Singular calls 'out' internaly
        singular_out = out.name()
        # We retrieve the Singular name of expr in the current session
        # so that we can call it from inside
        singular_expr = singular(expr).name()
        # Here we prepare what is going to be sent to Singular
        computemap = (
            # We create an initial poly
            "poly out = 0;"
            # This 'for' will loop over the rows of the Matrix
            # that is over every permutation of S_N
            "for(int i=1; i<=" + str(matrix_dim[0]) + "; i++){"
            # We define a map which will be the exchange operator
            "map f = basering, MM[i,1.." + str(matrix_dim[1]) + "];"
            # We apply the map and add the result to previous permutations
            "out = out + f(" + singular_expr + ");"
            "};" +
            # We define the 'out' known by Sage to be the Singular 'out'
            # This will update the value of out in Sage.
            singular_out + "= out;"
            "kill out;"
            "kill MM;"
        )
        # We send all of this to singular
        singular.eval(computemap)
        return out

    def var_to_monomials(self, expr, check_sym=True):
        """Take an expr in variables and return a {spart:coef} dict."""
        r"""
            If one is sure that the expression is indeed symmetric, on should
            set check_sym=False because this is a onerous operation, especialy
            with N>8.
        """
        if check_sym:
            if not self.is_symmetric(expr):
                expt_str = "This superpolynomial is not symmetric."
                raise Exception(expt_str)
        sector = self.get_sector(expr)
        ferm_degree = sector[1]
        if ferm_degree == 0:
            theta_1_m = 1
        else:
            theta_1_m = ['theta_'+str(k) for k in range(ferm_degree)]
            theta_1_m = singular('*'.join(theta_1_m))
        # Here we only take the part of expr that is multiplied by
        # theta_0...theta_ferm_degree because the rest of the expression
        # doesn't have more information.
        # In the following call:
        # the [1] is to select the power theta...^1
        # the [2] gives us the expression that multiplies theta...^1
        # Note that Singular indices start at 1
        projected_expr = expr.coef(theta_1_m)[1][2]

        theta_projected = theta_1_m*projected_expr
        # Now from this expression, we want to extract the coefficients
        # and superpartitions. To get the sign and multiplicity right, we must
        # make sure that the exponents of the x's are compatible with a
        # superpartition
        int_vecs = [mono.leadexp().sage() for mono in theta_projected]
        # Here I add a dummy element at the begining of int_vecs so that
        # indices matches those of theta_projected (which starts at 1)
        # This is only to limit confusion.
        int_vecs = [None] + int_vecs
        is_ordered = self._int_vec_is_ordered
        valid_vec = [k
                     for k in range(1, theta_projected.size() + 1)
                     if is_ordered(int_vecs[k])]
        to_spart = self._int_vec_to_spart
        # TODO verify that the coef are in the right ring
        spart_coef = {to_spart(int_vecs[k]): theta_projected[k].leadcoef()
                      for k in valid_vec}
        return spart_coef

    def monomial(self, spart):
        """Return the monomial expanded in terms of variables."""
        N = self._N
        # If we are under the stability limit, we send the monomial to zero.
        if len(spart) > N:
            return 0
        # We create a composition where fermionic parts are strings and bosonic
        # parts are int
        super_composition = ([str(part) for part in spart[0]] +
                             [part for part in spart[1]])
        # We extend the composition so that it fits with the number of vars
        add_zeros = [0 for k in range(N-len(super_composition))]
        super_composition = super_composition + add_zeros
        # We permute the elements of the compositions in every distinct ways
        permutations = unique_perm_list_elements(super_composition)
        # We get the permutations of the fermionic parts, this allows us to
        # compute the number of inversion that has occurend during the
        # permutation process. For each inversion the sign has to flip.
        ferm_perms = [[int(k) for k in a_perm if isinstance(k, str)]
                      for a_perm in permutations]
        inversions = [number_of_inversions(ferm_perm)
                      for ferm_perm in ferm_perms]

        # We construct the string expression for Singular to handle
        # This is a local method that take one element of the composition and
        # return the appropirate string
        def id_val_to_term(index, val):
            if isinstance(val, str):
                out = 'theta_' + str(index) + '*x_' + str(index) + '^'+val
            else:
                out = 'x_' + str(index) + '^' + str(val)
            return out
        # Maping the previous functions on every element we get the monomials
        monos_as_lists = [
            [id_val_to_term(k, a_comp[k])
             for k in range(len(a_comp))
             if a_comp[k] != 0]
            for a_comp in permutations]
        nb_monos = len(monos_as_lists)
        ferm_degree = spart.fermionic_degree()
        # We compute the overall sign (because we need the inverse number of
        # inversion for the sign to be right.
        over_all_sign = (((ferm_degree - 1) * ferm_degree) / 2)
        inversions = [over_all_sign + inv for inv in inversions]
        # We then generate every monomial
        monos = ['(-1)^' + str(inversions[k]) + '*' +
                 '*'.join(monos_as_lists[k])
                 for k in range(nb_monos)]
        # Adding them togeter we get the symmetric superpolynomial
        m_lambda = singular('+'.join(monos))
        return m_lambda

    def _slow_monomial(self, spart):
        """Old method for monomial genration."""
        N = self._N
        composition = list(spart[0]) + list(spart[1])
        super_ns_mono = self.ns_monomial(composition)
        if len(spart[0]) > 0:
            thetas = ['theta_%d' % (k)
                      for k in range(spart.fermionic_degree())]
            thetas = singular('*'.join(thetas))
            super_ns_mono = thetas*super_ns_mono
        symmed = self.symmetrize(super_ns_mono, len(composition))
        # For some reason I have to cast the number to QQ
        # Otherwise sage returns 0 for 1/normal. I have no idea why.
        normal = QQ(spart.n_lambda()*factorial(N - len(spart)))
        normal = singular(1/normal)
        super_mono = normal*symmed
        return super_mono

    def T_i(self, expr, i):
        """Apply the Cherednik generator i on expression."""
        SN = self._SN
        t = singular('t')
        X = self.x_vars()
        term1 = t*expr
        perm_expr = self.apply_permuation(expr, SN((i, i+1)))
        term2a = (t*X[i] - X[i+1])*(perm_expr - expr)
        term2 = term2a.division(X[i] - X[i+1])[1][1,1]
        return term1 + term2

    def Tw(self, expr, w):
        """Apply Ti for a list of elementary permutations."""
        if len(w) == 0:
            return expr
        apply_on = expr
        for i in w:
            apply_on = self.T_i(apply_on, i)
        return apply_on

    def _mac_from_ns(self, composition, mm):
        """Return the sMacdo obtained with the non-symmetric Macdonald."""
        r"""
            This is intended as a test method.
        """
        from sage.combinat.sf.ns_macdonald import E
        N = self._N
        q, t = QQ['q', 't'].fraction_field().gens()
        theta = self.theta_vars()
        # The ordering on composition is backward from ours.
        in_comp = composition
        in_comp.reverse()
        rev = range(1, N+1)
        rev.reverse()
        perm = Permutation(rev)
        # We have to permute the variables since the composition ordering is
        # backward, so must be the variables that is what pi=... does.
        ns_mac = E(in_comp, q, t, pi=perm)
        # We prepare the expression for singular
        string_list = str(ns_mac).split('x')
        singular_str = 'x_'.join(string_list)
        ns_mac_sing = singular(singular_str)
        # We generate the permutations [mm, ... N-1]
        Sslash = SymmetricGroup(range(mm, N))
        # Express them as chains of elementary permutations
        elem = [x.reduced_word() for x in Sslash]
        # We do the appropriate symmetrization
        terms = [self.Tw(ns_mac_sing, w) for w in elem]
        presc_mac = sum(terms).normalize()
        # We multiply by theta_0 ... theta_(m-1)
        super_presc = reduce(operator.mul, theta[:mm], 1)*presc_mac
        # Symmetrize the result
        macdo = self.symmetrize(super_presc).normalize()

        return macdo


def number_of_inversions(aList):
    """Return the number of inversion of a list."""
    inv_list = [
        sum(
            [
                1 for j in range(k, len(aList)) if aList[k] > aList[j]
            ])
        for k in range(len(aList) - 1)
    ]
    return sum(inv_list)
