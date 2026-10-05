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
            d_1_r_: int
            out0_: int
            out0_ = default__.product((default__.arg0)[d_0_i_], (default__.arg1)[d_0_i_])
            d_1_r_ = out0_
            _dafny.print(_dafny.string_of(d_1_r_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def product(a, b):
        result: int = int(0)
        result = (a) * (b)
        return result

    @staticmethod
    def Demo():
        d_0_r_: int
        out0_: int
        out0_ = default__.product(100000, 100000)
        d_0_r_ = out0_

    @_dafny.classproperty
    def arg0(instance):
        return _dafny.SeqWithoutIsStrInference([2147483647])
    @_dafny.classproperty
    def arg1(instance):
        return _dafny.SeqWithoutIsStrInference([1])

class int32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True

class int64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True
