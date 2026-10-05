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
            d_1_a_: int
            d_1_a_ = (default__.arg0)[d_0_i_]
            d_2_b_: int
            d_2_b_ = (default__.arg1)[d_0_i_]
            if ((d_2_b_) == (0)) or (((d_1_a_) == (-2147483648)) and ((d_2_b_) == (-1))):
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "skip\n"))).VerbatimString(False))
            elif True:
                d_3_q_: int
                out0_: int
                out0_ = default__.quot(d_1_a_, d_2_b_)
                d_3_q_ = out0_
                d_4_r_: int
                out1_: int
                out1_ = default__.rem(d_1_a_, d_2_b_)
                d_4_r_ = out1_
                _dafny.print(_dafny.string_of(d_3_q_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, " "))).VerbatimString(False))
                _dafny.print(_dafny.string_of(d_4_r_))
                _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def quot(a, b):
        result: int = int(0)
        result = _dafny.euclidian_division(a, b)
        return result

    @staticmethod
    def rem(a, b):
        result: int = int(0)
        result = _dafny.euclidian_modulus(a, b)
        return result

    @staticmethod
    def Demo():
        d_0_q_: int
        out0_: int
        out0_ = default__.quot(-7, 2)
        d_0_q_ = out0_
        d_1_r_: int
        out1_: int
        out1_ = default__.rem(-7, 2)
        d_1_r_ = out1_

    @_dafny.classproperty
    def arg0(instance):
        return _dafny.SeqWithoutIsStrInference([-7, 7, 5, -2147483648])
    @_dafny.classproperty
    def arg1(instance):
        return _dafny.SeqWithoutIsStrInference([2, -2, 0, -1])

class int32:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True
