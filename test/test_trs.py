from prologsolvers import trs
import janus_swi as janus


def test():
    janus.consult("trs", data=trs.code)
    assert janus.query_once("equations_trs([a = b, b = c, e = f], Rs)")
    assert False
