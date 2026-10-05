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
            d_1_v_: _dafny.Seq
            d_1_v_ = _dafny.SeqWithoutIsStrInference([((default__.arg0)[d_0_i_])[d_2_j_] for d_2_j_ in range(len((default__.arg0)[d_0_i_]))])
            d_3_r_: int
            out0_: int
            out0_ = default__.total(d_1_v_)
            d_3_r_ = out0_
            _dafny.print(_dafny.string_of(d_3_r_))
            _dafny.print((_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "\n"))).VerbatimString(False))

    @staticmethod
    def Sum(s):
        d_0___accumulator_ = 0
        while True:
            with _dafny.label():
                if (len(s)) == (0):
                    return (0) + (d_0___accumulator_)
                elif True:
                    d_0___accumulator_ = ((s)[(len(s)) - (1)]) + (d_0___accumulator_)
                    in0_ = _dafny.SeqWithoutIsStrInference((s)[:(len(s)) - (1):])
                    s = in0_
                    raise _dafny.TailCall()
                break

    @staticmethod
    def total(v):
        result: int = int(0)
        d_0_acc_: int
        d_0_acc_ = 0
        hi0_ = len(v)
        for d_1_i_ in range(0, hi0_):
            d_0_acc_ = (d_0_acc_) + ((v)[d_1_i_])
        result = d_0_acc_
        return result

    @_dafny.classproperty
    def arg0(instance):
        return _dafny.SeqWithoutIsStrInference([_dafny.SeqWithoutIsStrInference([]), _dafny.SeqWithoutIsStrInference([-9223372036854775808]), _dafny.SeqWithoutIsStrInference([1, 2, 3]), _dafny.SeqWithoutIsStrInference([2147483647, 2147483647])])

class int64:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
    def _Is(source__):
        return True
