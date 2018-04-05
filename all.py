from superpartition import Superpartitions
from sym_superfunct import SymSuperfunctionsAlgebra
from sage.rings.rational_field import QQ
from sage.structure.sage_object import load
load('superspace.py')


def super_init():
    """Inject the basis and the coeff ring."""
    global QQqta
    global Sym
    global Sparts
    QQqta = QQ['q', 't', 'alpha'].fraction_field()
    print("Defining QQqta as " + str(QQqta))
    Sym = SymSuperfunctionsAlgebra(QQqta)
    print("Defining Sym as " + str(Sym))
    Sym.inject_shorthands()
    Sparts = Superpartitions()
    print("Defining Sparts as " + str(Sparts))
