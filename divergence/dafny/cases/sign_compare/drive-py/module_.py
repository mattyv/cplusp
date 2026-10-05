import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_ as module_
import _dafny as _dafny
import System_ as System_

# Module: module_

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Main(noArgsParameter__):
        hi0_ = len(default__.arg0)
        for d_0_i_ in range(0, hi0_):
            d_1_r_: bool
            out0_: bool
            out0_ = default__.below((default__.arg0)[d_0_i_], (default__.arg1)[d_0_i_])
            d_1_r_ = out0_
            _dafny.print(_dafny.string_of(d_1_r_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def below(i, n):
        result: bool = False
        result = (i) < (n)
        return result

    @staticmethod
    def Demo():
        d_0_r_: bool
        out0_: bool
        out0_ = default__.below(-1, 1)
        d_0_r_ = out0_

    @_dafny.classproperty
    def arg0(instance):
        return _dafny.SeqWithoutIsStrInference([-1, 5, 0])
    @_dafny.classproperty
    def arg1(instance):
        return _dafny.SeqWithoutIsStrInference([3, 3, 0])

class int32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class uint64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True
