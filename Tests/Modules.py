

import unittest
import os
import sys
import subprocess
import networkx
import itertools

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))
sys.path.insert(0,BASE)

import PyBoolNet.FileExchange
import PyBoolNet.PrimeImplicants
import PyBoolNet.InteractionGraphs
import PyBoolNet.StateTransitionGraphs
import PyBoolNet.TrapSpaces
import PyBoolNet.ModelChecking
import PyBoolNet.AttractorDetection
import PyBoolNet.AttractorBasins
import PyBoolNet.QueryPatterns
import PyBoolNet.QuineMcCluskey
import PyBoolNet.Repository
import PyBoolNet.Utility

FILES_IN   = os.path.join(BASE, "PyBoolNet", "Tests", "Files", "Input")
FILES_OUT  = os.path.join(BASE, "PyBoolNet", "Tests", "Files")
config = PyBoolNet.Utility.Misc.myconfigparser.SafeConfigParser()
config.read(os.path.join(BASE, "PyBoolNet", "Dependencies", "settings.cfg"))


def run():
    unittest.main(verbosity=2, buffer=True, exit=False, module=__name__)


# for TestPyBoolNet.AttractorBasins
import json
from networkx.readwrite import json_graph


class TestUtility(unittest.TestCase):
    def test_dicts_are_consistent(self):
        x = {1:2}
        y = {}
        expected = True
        answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        x = {1:2,2:3}
        y = {2:3,3:4}
        expected = True
        answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        x = {1:2}
        y = {1:3}
        expected = False
        answer = PyBoolNet.Utility.Misc.dicts_are_consistent(x,y)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
    
class TestAttractorBasins(unittest.TestCase):
    def test_basin_diagram(self):
        primes = PyBoolNet.Repository.get_primes("arellano_rootstem")
        update = "asynchronous"
        attractors = PyBoolNet.TrapSpaces.trap_spaces(primes, "min")
        diagram = PyBoolNet.AttractorBasins.basins_diagram(primes, update, attractors, Silent=False)
        data = {'directed': True, 'graph': {'name': '()_with_int_labels'}, 'nodes': [{'formula': '(!AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 0, 'size': 128}, {'formula': '(!(AUXINS | (SCR | !(SHR))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 1, 'size': 64}, {'formula': '(!(AUXINS | !(JKD & (SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}], 'id': 2, 'size': 32}, {'formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 3, 'size': 8}, {'formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'attractors': [{u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 1, u'ARF': 0, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 0, u'AUXINS': 0, u'WOX': 0, u'IAA': 1, u'MGP': 0, u'ARF': 0, u'JKD': 0, u'SCR': 0}], 'id': 4, 'size': 32}, {'formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 5, 'size': 20}, {'formula': '(AUXINS&!SHR)', 'attractors': [{u'SHR': 0, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 6, 'size': 128}, {'formula': '(!((SCR | !(SHR)) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}], 'id': 7, 'size': 64}, {'formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 0, u'SCR': 0}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 8, 'size': 2}, {'formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}, {u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 9, 'size': 20}, {'formula': '(!(((IAA | !(JKD & (SCR & (SHR & (WOX))) | !JKD & !(MGP | !(SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 1, u'IAA': 0, u'MGP': 0, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 10, 'size': 6}, {'formula': '(!((((((WOX) | !SHR) | !SCR) | !MGP) | !JKD) | !AUXINS))', 'attractors': [{u'SHR': 1, u'PLT': 1, u'AUXINS': 1, u'WOX': 0, u'IAA': 0, u'MGP': 1, u'ARF': 1, u'JKD': 1, u'SCR': 1}], 'id': 11, 'size': 8}], 'links': [{'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'target': 11, 'source': 3, 'finally_size': 8}, {'finally_formula': '(!((JKD | ((((WOX) | !SHR) | !SCR) | !MGP)) | !AUXINS))', 'target': 7, 'source': 3, 'finally_size': 8}, {'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'target': 1, 'source': 4, 'finally_size': 32}, {'finally_formula': '(!(AUXINS | (JKD | !(SCR & (SHR)))))', 'target': 2, 'source': 4, 'finally_size': 32}, {'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'target': 8, 'source': 5, 'finally_size': 6}, {'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'target': 9, 'source': 5, 'finally_size': 20}, {'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'target': 10, 'source': 5, 'finally_size': 20}, {'finally_formula': '(!(ARF & ((IAA & (JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & (JKD | (MGP | (((WOX) | !SHR) | !SCR)))) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !AUXINS)))', 'target': 3, 'source': 5, 'finally_size': 20}, {'finally_formula': '(!(ARF & (((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !IAA) | !AUXINS) | !ARF & ((JKD | !(MGP & (SCR & (SHR & (WOX))))) | !AUXINS)))', 'target': 7, 'source': 5, 'finally_size': 6}, {'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'target': 10, 'source': 8, 'finally_size': 2}, {'finally_formula': '(!(((IAA | (JKD | !(MGP & (SCR & (SHR & (WOX)))))) | !AUXINS) | !ARF))', 'target': 7, 'source': 8, 'finally_size': 2}, {'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'target': 10, 'source': 9, 'finally_size': 20}, {'finally_formula': '(ARF & (AUXINS & (IAA & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR)))) | !IAA & !((MGP | (((WOX) | !SHR) | !SCR)) | !JKD))) | !ARF & (AUXINS & (JKD & (MGP & (SCR & (SHR & (WOX))) | !MGP & (SCR & (SHR))))))', 'target': 11, 'source': 9, 'finally_size': 20}], 'multigraph': False}
        expected = json_graph.node_link_graph(data)
                
        self.assertTrue(PyBoolNet.AttractorBasins.diagrams_are_equal(diagram, expected))
                
        fname_out = os.path.join(FILES_OUT, "basin_diagram.pdf")
                
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleInputs=True)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleInputs=False)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, FnameATTRACTORS=fname_out)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleRanks=True)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleFillColor=True)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleSplines="ortho")
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleEdges=True)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, StyleRefinement=True)
        PyBoolNet.AttractorBasins.diagram2image(primes, diagram, FnameIMAGE=fname_out, FirstIndex=10)
        PyBoolNet.AttractorBasins.diagram2aggregate_image(primes, diagram, FnameIMAGE=fname_out)
        
        
        

class TestRepository(unittest.TestCase):
    def test_calls(self):
        PyBoolNet.Repository.get_all_names()
        PyBoolNet.Repository.get_primes("raf")
        PyBoolNet.Repository.get_bnet("raf")


class TestQuineMcCluskey(unittest.TestCase):
    def test_functions2mindnf(self):
        bfunctions = {'v1': lambda v1,v2: v1 or not v2, 'v2': lambda v1: not v1,
                      'v3': lambda : False, 'v4': lambda v3: v3 or not v3}

        answer = PyBoolNet.QuineMcCluskey.functions2mindnf(bfunctions)
        expected = {'v1': '((! v2) | v1)', 'v2': '(! v1)', 'v3': '0', 'v4': '1'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    def test_primes2mindnf(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}

        answer = PyBoolNet.QuineMcCluskey.primes2mindnf(primes)
        expected = {'A': '0', 'C': '(B & (! A))', 'B': '1'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        

class TestStateTransitionGraphs(unittest.TestCase):
    def test_list_states_referenced_by_proposition(self):
        primes = PyBoolNet.Repository.get_primes("raf")
        prop = "!Erk | (Raf & Mek)"
        expected = set(["010","011","001","000","111"])
        answer = set(PyBoolNet.StateTransitionGraphs.list_states_referenced_by_proposition(primes, prop))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        prop = "0"
        expected = set([])
        answer = set(PyBoolNet.StateTransitionGraphs.list_states_referenced_by_proposition(primes, prop))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        prop = "TRUE"
        expected = set(["010","011","001","000","111","110","101","100"])
        answer = set(PyBoolNet.StateTransitionGraphs.list_states_referenced_by_proposition(primes, prop))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
    def test_random_mixed_transition(self):
        fname_in  = os.path.join(FILES_IN,  "randomnet.bnet")
        fname_out = os.path.join(FILES_OUT, "randomnet.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        PyBoolNet.StateTransitionGraphs.random_successor_mixed(primes, state)
        # no assertion

        
    def test_successors_asynchronous(self):
        fname_in  = os.path.join(FILES_IN,  "randomnet.bnet")
        fname_out = os.path.join(FILES_OUT, "randomnet.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        PyBoolNet.StateTransitionGraphs.successors_asynchronous(primes, state)
        # no assertion
        
    def test_successor_synchronous(self):
        fname_in  = os.path.join(FILES_IN,  "randomnet.bnet")
        fname_out = os.path.join(FILES_OUT, "randomnet.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        PyBoolNet.StateTransitionGraphs.successor_synchronous(primes, state)
        # no assertion


    def test_best_first_reachability(self):
        fname_in  = os.path.join(FILES_IN,  "randomnet.bnet")
        fname_out = os.path.join(FILES_OUT, "randomnet.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        initialspace = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        goalspace = {'Gene2':0,'Gene4':0,'Gene6':0,'Gene8':0}
        memory = 10000
        path = PyBoolNet.StateTransitionGraphs.best_first_reachability(primes, initialspace, goalspace, memory)
        self.assertTrue(path!=None)

    def test_state2str(self):
        state = {"v2":0, "v1":1, "v3":1}
        
        answer = PyBoolNet.StateTransitionGraphs.state2str(state)
        expected = "101"
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    def test_primes2stg(self):
        fname_in  = os.path.join(FILES_IN,  "irma.primes")
        fname_out = os.path.join(FILES_OUT, "irma_stg.pdf")

        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        init = lambda x: x["Cbf1"]+x["Ash1"]+x["Gal80"]==1

        PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous", InitialStates=init)
        PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)

        init = []
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = stg.nodes()
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        init = ["000010"]
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = sorted(stg.nodes())
        expected = ['000010', '000110']
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)


        init = [{'Cbf1':0, 'Gal4':1, 'Gal80':0, 'gal':1, 'Swi5':0, 'Ash1':1}]
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = sorted(stg.nodes())
        expected = ['010001', '010011', '100011', '101001']
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
    def test_stg2dot(self):
        fname_in  = os.path.join(FILES_IN,  "irma.primes")
        fname_out = os.path.join(FILES_OUT, "irma_stg.dot")

        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.stg2dot(stg, fname_out)
        # no assertion

    def test_stg2image(self):
        fname_in  = os.path.join(FILES_IN,  "irma.primes")
        fname_out1 = os.path.join(FILES_OUT, "irma_stg_async.pdf")
        fname_out2 = os.path.join(FILES_OUT, "irma_stg_tendencies_async.pdf")
        fname_out3 = os.path.join(FILES_OUT, "irma_stg_sccs_async.pdf")

        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out1)

        PyBoolNet.StateTransitionGraphs.add_style_tendencies(stg)
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out2)

        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.add_style_sccs(stg)
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out3)

        fname_out1 = os.path.join(FILES_OUT, "irma_stg_sync.pdf")
        fname_out2 = os.path.join(FILES_OUT, "irma_stg_tendencies_sync.pdf")
        fname_out3 = os.path.join(FILES_OUT, "irma_stg_sccs_sync.pdf")
        fname_out4 = os.path.join(FILES_OUT, "irma_stg_path.pdf")

        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out1)

        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.add_style_tendencies(stg)
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out2)

        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        PyBoolNet.StateTransitionGraphs.add_style_sccs(stg)
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out3)


        init = PyBoolNet.StateTransitionGraphs.random_state(Primes=primes)
        walk = PyBoolNet.StateTransitionGraphs.random_walk(Primes=primes, Update="asynchronous", InitialState=init, Length=5)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        PyBoolNet.StateTransitionGraphs.add_style_path(stg, walk, "red")
        init = PyBoolNet.StateTransitionGraphs.random_state(Primes=primes)
        walk = PyBoolNet.StateTransitionGraphs.random_walk(Primes=primes, Update="asynchronous", InitialState=init, Length=5)
        PyBoolNet.StateTransitionGraphs.add_style_path(stg, walk, "blue")
        PyBoolNet.StateTransitionGraphs.stg2image(stg, fname_out4)
        # no assertion
        
        
    def test_random_state(self):
        fname_in  = os.path.join(FILES_IN,  "irma.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        PyBoolNet.StateTransitionGraphs.random_state(Primes=primes)
        PyBoolNet.StateTransitionGraphs.random_state(Primes=primes, Subspace="111-0-")
        # no assertion

    def test_stg2sccgraph(self):
        fname_out = os.path.join(FILES_OUT, "raf_sccgraph.pdf")
        primes = PyBoolNet.Repository.get_primes("raf")
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
        sccg = PyBoolNet.StateTransitionGraphs.stg2sccgraph(stg)
        PyBoolNet.StateTransitionGraphs.sccgraph2image(sccg, fname_out)
        # no assertion

    def test_stg2condensationgraph(self):
        fname_out = os.path.join(FILES_OUT, "raf_cgraph.pdf")
        primes = PyBoolNet.Repository.get_primes("raf")
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
        cgraph = PyBoolNet.StateTransitionGraphs.stg2condensationgraph(stg)
        PyBoolNet.StateTransitionGraphs.condensationgraph2image(cgraph, fname_out)
        # no assertion

    def test_stg2htg(self):
        fname_out = os.path.join(FILES_OUT, "raf_htg.pdf")
        primes = PyBoolNet.Repository.get_primes("raf")
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
        htg = PyBoolNet.StateTransitionGraphs.stg2htg(stg)
        PyBoolNet.StateTransitionGraphs.htg2image(htg, fname_out)
        # no assertion
        



class TestAttractorDetection(unittest.TestCase):

    def test_attractor_representatives(self):
        # not finished
        return
    
        bnet = """
        v1, !v1&v2&v3 | v1&!v2 | v1&!v3
        v2, !v1&!v2 | v1&v2&v3
        v3, !v1&v3 | v2&v3
        """

        # [steadystates,cyclic]
        # identical for sync/async updates
        steadystates_expected = ["100"]
        cyclic_attractors = [["010","000"],["001","011","111"]]
        
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        for update in ["asynchronous","synchronous"]:
            steadystates, cyclic = PyBoolNet.AttractorDetection.compute_attractor_representatives(primes, update)
            
            for x in steadystates:
                msg = "\nexpected one of: "+str(steadystates_expected)
                msg+= "\ngot:             "+str(x)
                self.assertTrue(x in steadystates_expected, msg)

            for x in cyclic:
                msg = "\nexpected one of: "+str(cyclic_attractors)
                msg+= "\ngot:             "+str(x)
                self.assertTrue( sum(x in Y for Y in cyclic_attractors)==1, msg)

        # positive cycle with output component
        bnet = "v1, v2 \n v2, v1 \n v3, v2"
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        update = "asynchronous"
        steadystates_expected = ["111","000"]
        cyclic_attractors = []
        steadystates, cyclic = PyBoolNet.AttractorDetection.compute_attractor_representatives(primes, update)

        for x in steadystates:
            msg = "\nexpected one of: "+str(steadystates_expected)
            msg+= "\ngot:             "+str(x)
            self.assertTrue(x in steadystates_expected, msg)

        for x in cyclic:
            msg = "\nexpected one of: "+str(cyclic_attractors)
            msg+= "\ngot:             "+str(x)
            self.assertTrue( sum(x in Y for Y in cyclic_attractors)==1, msg)


        for name in PyBoolNet.Repository.get_all_names():
            primes = PyBoolNet.Repository.get_primes(name)
            if len(primes)>10: continue
            
            for update in ["asynchronous", "synchronous", "mixed"]:
                stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, update)
                steady_tarjan, cyclic_tarjan = PyBoolNet.AttractorDetection.compute_attractors_tarjan(stg)
                steady_rep, cyclic_rep = PyBoolNet.AttractorDetection.compute_attractor_representatives(primes, update)

                k1 = len(steady_tarjan)+len(cyclic_tarjan)
                k2 = len(steady_rep)+len(cyclic_rep)
                msg = "\ntarjan finds %i attractors."%k1
                msg+= "\nreps finds %i attractors."%k2
                self.assertTrue(k1==k2, msg)

                
        
        update = "asynchronous"
        for name in PyBoolNet.Repository.get_all_names():
            print name
            primes = PyBoolNet.Repository.get_primes(name)
            if len(primes)>10: continue
            steadystates, cyclic = PyBoolNet.AttractorDetection.compute_attractor_representatives(primes, update)
            expected = len(PyBoolNet.TrapSpaces.trap_spaces(primes,"min"))
            got = len(steadystates)+len(cyclic)
            msg = "\nname:      "+name
            msg+= "\nexpected : "+str(expected)
            msg+= "\ngot:       "+str(got)
            self.assertTrue(expected==got, msg)
            
    def test_compute_attractors_tarjan(self):
        bnet = ["x, !x&y | z",
                "y, !x | !z",
                "z, x&!y"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "asynchronous")
        steadystates, cyclic = PyBoolNet.AttractorDetection.compute_attractors_tarjan(stg)

        steady_expected = ["101"]
        cyclic_expected = [set(["010","110"])]

        msg = "\nexpected: "+str(steady_expected)
        msg+= "\ngot:      "+str(steadystates)
        self.assertTrue(steadystates==steady_expected, msg)

        msg = "\nexpected: "+str(cyclic_expected)
        msg+= "\ngot:      "+str(cyclic)
        self.assertTrue(cyclic==cyclic_expected, msg)
        
    def test_find_attractor_state_by_randomwalk_and_ctl(self):
        fname_in  = os.path.join(FILES_IN,  "randomnet.bnet")
        fname_out = os.path.join(FILES_OUT, "randomnet.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        subspace = {'Gene1':0,'Gene3':0,'Gene5':0,'Gene7':0,'Gene9':0}
        lengthrandomwalk = 200
        attempts = 10
        update = "asynchronous"
        PyBoolNet.AttractorDetection.find_attractor_state_by_randomwalk_and_ctl(primes, update, subspace, lengthrandomwalk, attempts)
        update = "synchronous"
        PyBoolNet.AttractorDetection.find_attractor_state_by_randomwalk_and_ctl(primes, update, subspace, lengthrandomwalk, attempts)
        update = "mixed"
        PyBoolNet.AttractorDetection.find_attractor_state_by_randomwalk_and_ctl(primes, update, subspace, lengthrandomwalk, attempts)
        # no assertion
        
    def test_univocality(self):

        # not univocal
        bnet= ["v1, !v1&!v2 | v2&!v3",
               "v2, v1&v2",
               "v3, v2 | v3",
               "v4, 1"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        trapspace = {"v4":1}
        answer = PyBoolNet.AttractorDetection.univocality(primes, "asynchronous", trapspace)
        expected = False
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        trapspace = {}
        answer, counterex = PyBoolNet.AttractorDetection.univocality_with_counterexample(primes, "asynchronous", trapspace)
        expected = (4,4)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str((len(counterex[0]), len(counterex[1])))
        self.assertTrue((len(counterex[0]), len(counterex[1]))==expected, msg)

        bnet =  """
                v1, 0
                v2, v2
                """
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        trapspace = {"v1":0}
        answer, counterex = PyBoolNet.AttractorDetection.univocality_with_counterexample(primes, "asynchronous", trapspace)
        expected = [{"v1":0,"v2":0},{"v1":0,"v2":1}]
        self.assertTrue(counterex[0] in expected)
        self.assertTrue(counterex[1] in expected)
        self.assertTrue(len(counterex)==2)        

        # univocal with unique steady state

        bnet= ["v1, !v1&!v2 | !v3",
               "v2, v1&v2",
               "v3, v1&v3 | v2",
               "v4, 0"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        trapspace = {}
        answer, counterex = PyBoolNet.AttractorDetection.univocality_with_counterexample(primes, "asynchronous", trapspace)
        expected = None
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue(counterex==expected, msg)
        
        answer = PyBoolNet.AttractorDetection.univocality(primes, "asynchronous", trapspace)
        expected = True
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        

    def test_faithfulness(self):
        
        bnet = ["v1, !v1&!v2 | !v2&!v3",
                "v2, !v1&!v2&v3 | v1&!v3",
                "v3, !v1&v3 | !v2"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        # not faithful
        trapspace = {}
        answer = PyBoolNet.AttractorDetection.faithfulness(primes, "asynchronous", trapspace)
        expected = False
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        # faithful
        trapspace = {"v3":1}
        answer = PyBoolNet.AttractorDetection.faithfulness(primes, "asynchronous", trapspace)
        expected = True
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        # not faithful due to percolation
        bnet =  """
                v1, 0
                v2, v1
                v3, v3
                """
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        trapspace = {"v1":0}
        expected = False
        
        answer, counterex = PyBoolNet.AttractorDetection.faithfulness_with_counterexample(primes, "asynchronous", trapspace)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        expected_counterex = [{"v1":0,"v2":0,"v3":0},{"v1":0,"v2":0,"v3":1}]
        msg = "\nexpected on of: "+str(expected_counterex)
        msg+= "\ngot:            "+str(counterex)
        self.assertTrue(counterex in expected_counterex, msg)
        
        
    def test_completeness_naive(self):
        
        bnet= ["v1, v1 | v2&!v3",
               "v2, !v1&v2&v3",
               "v3, !v2&!v3 | v2&v3"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        # not complete
        subspaces = ["00-","10-"]
        expected  = False
        answer, counterex = PyBoolNet.AttractorDetection.completeness_naive(primes, "asynchronous", subspaces)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)


        # complete
        subspaces = ["00-","10-", {"v1":0,"v2":1,"v3":1}]
        expected  = True
        answer, counterex = PyBoolNet.AttractorDetection.completeness_naive(primes, "asynchronous", subspaces)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    def test_completeness(self):

        bnet = ["v0,   v0",
                "v1,   v2",
                "v2,   v1",
                "v3,   v1&v0",
                "v4,   v2",
                "v5,   v3&!v6",
                "v6,   v4&v5"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        expected = True
        answer = PyBoolNet.AttractorDetection.completeness(primes, "asynchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        expected = False
        answer = PyBoolNet.AttractorDetection.completeness(primes, "synchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        answer, counterex = PyBoolNet.AttractorDetection.completeness_with_counterexample(primes, "synchronous")
        counterex = PyBoolNet.StateTransitionGraphs.state2str(counterex)
        stg = PyBoolNet.StateTransitionGraphs.primes2stg(primes, "synchronous")
        
        for x in PyBoolNet.TrapSpaces.trap_spaces(primes, "min"):
            x = PyBoolNet.StateTransitionGraphs.subspace2str(primes,x)
            msg = "\n%s is a completeness counterexample but it can reach"%counterex
            msg+= "\nthe minimal trap space %s"%x
            X = PyBoolNet.StateTransitionGraphs.list_states_in_subspace(primes,x)
            X = [PyBoolNet.StateTransitionGraphs.state2str(x) for x in X]
            result = PyBoolNet.Utility.DiGraphs.has_path(stg, counterex, X)

            self.assertTrue(result==False, msg)
            
        bnet= ["v1, !v1&v2&v3 | v1&!v2&!v3",
               "v2, !v1&!v2 | v1&v3",
               "v3, !v1&v3 | v1&v2",
               "v4, 1",
               "v5, v4"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        # not complete
        expected  = False
        answer = PyBoolNet.AttractorDetection.completeness(primes, "asynchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        answer, counterex = PyBoolNet.AttractorDetection.completeness_with_counterexample(primes, "asynchronous")
        expected = len(primes)
        got = len(counterex)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(got)
        self.assertTrue(got==expected, msg)

        # complete
        expected = True
        answer = PyBoolNet.AttractorDetection.completeness(primes, "synchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
        bnet = ["v1, !v1&v2&v3 | v1&!v2&!v3",
                "v2, !v1&!v2 | v1&v3",
                "v3, v2 | v3"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        # complete
        expected = True
        answer = PyBoolNet.AttractorDetection.completeness(primes, "asynchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        answer = PyBoolNet.AttractorDetection.completeness(primes, "synchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        bnet = ["v1,   !v2",
                "v2,   v1",
                "v3,   v1",
                "v4,   v2",
                "v5,   v6",
                "v6,   v4&v5",
                "v7,   v2",
                "v8,   v5",
                "v9,   v6&v10",
                "v10,  v9&v7"]
        bnet = "\n".join(bnet)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        expected = True
        answer = PyBoolNet.AttractorDetection.completeness(primes, "synchronous")
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        

class TestTemporalQueries(unittest.TestCase):
    def test_EF_subspaces(self):
        subspaces = [{'v1':0,'v2':0}, {'v1':1,'v2':1}]
        names = ["v1","v2"]
        expected  = 'EF(!v1&!v2 | v1&v2)'
        query = PyBoolNet.QueryPatterns.EF_oneof_subspaces(names, subspaces)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(query)
        self.assertTrue(query==expected, msg)

    def EF_unsteady(self):
        names = ['v1','v2','v3']
        expected  = 'EF(v1_unsteady) & EF(v2_unsteady) & EF(v3_unsteady)'
        query = PyBoolNet.QueryPatterns.EF_unsteady_states(names)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(query)
        self.assertTrue(query==expected, msg)

    def test_AGEF_subspaces(self):
        subspaces = [{'v1':0,'v2':0},{'v2':1}]
        names = ["v1","v2"]
        expected  = 'AG(EF(!v1&!v2 | v2))'
        query = PyBoolNet.QueryPatterns.AGEF_oneof_subspaces(names, subspaces)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(query)
        self.assertTrue(query==expected, msg)


class TestModelChecking(unittest.TestCase):
    def test_accepting_states(self):
        bnet = """
        Erk, Raf&Mek | Mek&Erk
	Mek, Raf&Mek | Erk
	Raf, !Raf | !Erk
        """

        fname_out = os.path.join(FILES_OUT, "modelchecking_acceptingstates.smv")
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        
        spec = "CTLSPEC EF(!Erk&!Mek&Raf) &  EF(Erk&Mek&Raf)"
        init = "INIT TRUE"
        update = "asynchronous"

        PyBoolNet.ModelChecking.primes2smv(primes, update, init, spec, fname_out)
        answer, accepting = PyBoolNet.ModelChecking.check_smv_with_acceptingstates(fname_out)

        expected = {'ACCEPTING_SIZE': 3, 'INIT': 'TRUE', 'INIT_SIZE': 8, 'INITACCEPTING_SIZE': 3, 'INITACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))', 'ACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(accepting)
        self.assertTrue(accepting==expected, msg)

        answer, accepting = PyBoolNet.ModelChecking.check_primes_with_acceptingstates(primes, update, init, spec)
        expected = {'ACCEPTING_SIZE': 3, 'INIT': 'TRUE', 'INIT_SIZE': 8, 'INITACCEPTING_SIZE': 3, 'INITACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))', 'ACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(accepting)
        self.assertTrue(accepting==expected, msg)
        
        
    def test_check_smv_true(self):
        fname_in  = os.path.join(FILES_IN,  "modelchecking_check_smv_true.smv")

        self.assertTrue(PyBoolNet.ModelChecking.check_smv(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True))
        
    def test_check_smv_false(self):
        fname_in  = os.path.join(FILES_IN,  "modelchecking_check_smv_false.smv")

        self.assertFalse(PyBoolNet.ModelChecking.check_smv(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True))
        

    def test_check_smv_counterexample(self):
        fname_in  = os.path.join(FILES_IN,  "modelchecking_check_smv_counterexample.smv")

        answer, counterex = PyBoolNet.ModelChecking.check_smv_with_counterexample(FnameSMV=fname_in, DynamicReorder=True, DisableReachableStates=True)


        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})
        
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue(counterex==expected, msg)
        

    def test_check_primes_async(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}
        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})

        answer, counterex = PyBoolNet.ModelChecking.check_primes_with_counterexample(Primes=primes, Update="asynchronous", InitialStates="INIT !v1&v2&!v3", Specification="CTLSPEC AF(!v1&!v2&v3)", DynamicReorder=True, DisableReachableStates=False)

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue(counterex==expected, msg)
        

    def test_check_primes_sync(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}
        

        expected = None
        
        answer, counterex = PyBoolNet.ModelChecking.check_primes_with_counterexample(Primes=primes, Update="synchronous", InitialStates="INIT !v1&v2&!v3", Specification="CTLSPEC AF(!v1&!v2&v3)", DynamicReorder=True, DisableReachableStates=False)

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue(counterex==expected, msg)
        

    def test_check_primes_mixed(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}


        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})

        answer, counterex = PyBoolNet.ModelChecking.check_primes_with_counterexample(Primes=primes, Update="mixed", InitialStates="INIT !v1&v2&!v3", Specification="CTLSPEC AF(!v1&!v2&v3)", DynamicReorder=True, DisableReachableStates=False)

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue(counterex==expected, msg)


class TestTrapSpaces(unittest.TestCase):
    def test_trap_spaces_piped1(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="min")
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)
        

    def test_trap_spaces_piped2(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_tsfree.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="min")
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)
        
        
    def test_trap_spaces_tsfree(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_tsfree.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_tsfree_min.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="min", FnameASP=fname_out)
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)        

        fname_in  = os.path.join(FILES_IN,  "trapspaces_tsfree.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_tsfree_all.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="all", FnameASP=fname_out)
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

        fname_in  = os.path.join(FILES_IN,  "trapspaces_tsfree.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_tsfree_max.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="max", FnameASP=fname_out)
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

        
    def test_trap_spaces_posfeedback_min(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_posfeedback_min.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="min", FnameASP=fname_out)
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

    def test_trap_spaces_posfeedback_max(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_posfeedback_max.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="max", FnameASP=fname_out)
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

    def test_trap_spaces_posfeedback_all(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_posfeedback_all.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces(Primes=primes, Type="all", FnameASP=fname_out)
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{},{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

    def test_trap_spaces_posfeedback_bounds1(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_posfeedback_bounds1.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces_bounded(Primes=primes, Type="all", Bounds=(1,2), FnameASP=fname_out)
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

    def test_trap_spaces_posfeedback_bounds2(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_posfeedback.primes")
        fname_out = os.path.join(FILES_OUT, "trapspaces_posfeedback_bounds2.asp")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)

        tspaces = PyBoolNet.TrapSpaces.trap_spaces_bounded(Primes=primes, Type="max", Bounds=(0,100), FnameASP=fname_out)
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue(tspaces==expected, msg)

    def test_trap_spaces_bounded(self):
        fname_in  = os.path.join(FILES_IN,  "trapspaces_bounded.bnet")
        fname_out  = os.path.join(FILES_IN,  "trapspaces_bounded.primes")
        primes = PyBoolNet.FileExchange.bnet2primes(fname_in, fname_out)

        tspaces_all = PyBoolNet.TrapSpaces.trap_spaces(primes, "all")
        tspaces_all.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{},
                    {"v3":1},
                    {"v3":0},
                    {"v1":1},
                    {"v1":1,"v2":1},
                    {"v1":0,"v2":0},
                    {"v3":1,"v4":1},
                    {"v1":1,"v3":0},
                    {"v1":1,"v3":1},
                    {"v1":1,"v2":1,"v3":1},
                    {"v1":1,"v3":1,"v4":1},
                    {"v1":1,"v2":1,"v3":0},
                    {"v1":0,"v2":0,"v3":0},
                    {"v1":0,"v2":0,"v3":1},
                    {"v1":1,"v2":1,"v4":1},
                    {"v1":0,"v2":0,"v3":1,"v4":1},
                    {"v1":1,"v2":1,"v3":0,"v4":1},
                    {"v1":1,"v2":1,"v3":1,"v4":1},
                    {"v1":0,"v2":0,"v3":0,"v4":0},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_all)
        self.assertTrue(tspaces_all==expected, msg)
        
        tspaces_min = PyBoolNet.TrapSpaces.trap_spaces(primes, "min")
        tspaces_min.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [
                    {"v1":0,"v2":0,"v3":0,"v4":0},
                    {"v1":1,"v2":1,"v3":1,"v4":1},
                    {"v1":0,"v2":0,"v3":1,"v4":1},
                    {"v1":1,"v2":1,"v3":0,"v4":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_min)
        self.assertTrue(tspaces_min==expected, msg)

        
        tspaces_max = PyBoolNet.TrapSpaces.trap_spaces(primes, "max")
        tspaces_max.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"v3":1},
                    {"v3":0},
                    {"v1":1},
                    {"v1":0,"v2":0},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_max)
        self.assertTrue(tspaces_max==expected, msg)

        tspaces_bounded = PyBoolNet.TrapSpaces.trap_spaces_bounded(primes, "max", Bounds=(1,1))
        tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"v3":1},
                    {"v3":0},
                    {"v1":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_bounded)
        self.assertTrue(tspaces_bounded==expected, msg)

        tspaces_bounded = PyBoolNet.TrapSpaces.trap_spaces_bounded(primes, "max", Bounds=(2,3))
        tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"v1":1,"v2":1},
                    {"v1":0,"v2":0},
                    {"v3":1,"v4":1},
                    {"v1":1,"v3":0},
                    {"v1":1,"v3":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_bounded)
        self.assertTrue(tspaces_bounded==expected, msg)

        tspaces_bounded = PyBoolNet.TrapSpaces.trap_spaces_bounded(primes, "all", Bounds=(2,3))
        tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [
                    {"v1":1,"v2":1},
                    {"v1":0,"v2":0},
                    {"v3":1,"v4":1},
                    {"v1":1,"v3":0},
                    {"v1":1,"v3":1},
                    {"v1":1,"v2":1,"v3":1},
                    {"v1":1,"v3":1,"v4":1},
                    {"v1":1,"v2":1,"v3":0},
                    {"v1":0,"v2":0,"v3":0},
                    {"v1":0,"v2":0,"v3":1},
                    {"v1":1,"v2":1,"v4":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_bounded)
        self.assertTrue(tspaces_bounded==expected, msg)


        tspaces_bounded = PyBoolNet.TrapSpaces.trap_spaces_bounded(primes, "min", Bounds=(2,3))
        tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [
                    {"v1":1,"v2":1,"v3":1},
                    {"v1":1,"v3":1,"v4":1},
                    {"v1":1,"v2":1,"v3":0},
                    {"v1":0,"v2":0,"v3":0},
                    {"v1":0,"v2":0,"v3":1},
                    {"v1":1,"v2":1,"v4":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_bounded)
        self.assertTrue(tspaces_bounded==expected, msg)


    def test_steady_states_projected(self):
        lines = ["x,    !x&!y | x&y",
                 "y,    y",
                 "z,    z"]
        bnet = "\n".join(lines)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        # network has 4 steady states: 010,110,011,111

        result = PyBoolNet.TrapSpaces.steady_states_projected(primes, ["y"], Aggregate=True)
        expected = [({"y":1},4)]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)

        result = PyBoolNet.TrapSpaces.steady_states_projected(primes, ["y","x"], Aggregate=False)
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"x":0, "y":1}, {"x":1, "y":1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)


    def test_trap_spaces_inside_and_outside(self):
        lines = ["x,    !x&!y | x&y",
                 "y,    y",
                 "z,    z"]
        bnet = "\n".join(lines)
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        """
        trap spaces "all":
        {}
        {'y': 0}
        {'y': 1}
        {'z': 0}
        {'z': 1}
        {'y': 1, 'x': 0}
        {'y': 1, 'x': 1}
        {'y': 0, 'z': 0}
        {'y': 0, 'z': 1}
        {'y': 1, 'z': 0}
        {'y': 1, 'z': 1}
        {'y': 1, 'x': 0, 'z': 0}
        {'y': 1, 'x': 0, 'z': 1}
        {'y': 1, 'x': 1, 'z': 0}
        {'y': 1, 'x': 1, 'z': 1}
        """

        result = PyBoolNet.TrapSpaces.trap_spaces_outsideof(primes, "all", OutsideOf={'y': 0, 'z': 1})
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}, {'y': 0}, {'y': 0, 'z': 1}, {'z': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)

        result = PyBoolNet.TrapSpaces.trap_spaces_insideof(primes, "all", InsideOf={'y': 1, 'x': 0})
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'y': 1, 'x': 0}, {'y': 1, 'x': 0, 'z': 0}, {'y': 1, 'x': 0, 'z': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)


    def test_encoding_bijection(self):
        """
        The mapping from stable and consistent prime implicant sets to trap spaces is surjective but not injective.
        Two different arc sets may lead to the same trap space.
        In the following example there are four trap stable+consistent arc sets but only two trap spaces.
        """

        bnet = "\n".join(["v1,v1|v2","v2,v1"])
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        result = PyBoolNet.TrapSpaces.trap_spaces(primes, "all")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}, {'v1': 0, 'v2': 0}, {'v1': 1}, {'v1': 1, 'v2': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)
        
        result = PyBoolNet.TrapSpaces.trap_spaces(primes, "min")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0}, {'v1': 1, 'v2': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)
        
        result = PyBoolNet.TrapSpaces.trap_spaces(primes, "max")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0}, {'v1': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==expected, msg)
        
        
        

class TestPrimeImplicants(unittest.TestCase):
    def test_rename(self):
        primes = PyBoolNet.Repository.get_primes("raf")
        PyBoolNet.PrimeImplicants.rename_variable(primes, "Raf", "Raf23")
        expected = {'Raf23': [[{'Raf23': 1, 'Erk': 1}], [{'Raf23': 0}, {'Erk': 0}]], 'Mek': [[{'Raf23': 0, 'Erk': 0}, {'Mek': 0, 'Erk': 0}], [{'Mek': 1, 'Raf23': 1}, {'Erk': 1}]], 'Erk': [[{'Raf23': 0, 'Erk': 0}, {'Mek': 0}], [{'Mek': 1, 'Raf23': 1}, {'Mek': 1, 'Erk': 1}]]}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(primes)
        self.assertTrue(primes==expected, msg)
        self.assertRaises(Exception, PyBoolNet.PrimeImplicants.rename_variable, primes, "GADD", "GADD12")

        
    def test_create_disjoint_union(self):
        primes1 = PyBoolNet.FileExchange.bnet2primes("A, B \n B, !A")
        primes2 = PyBoolNet.FileExchange.bnet2primes("C, D \n D, C")
        primes = PyBoolNet.FileExchange.bnet2primes("A, B \n B, !A \n C, D \n D, C")
        result = PyBoolNet.PrimeImplicants.create_disjoint_union(primes1, primes2)
        msg = "\nexpected: "+str(primes)
        msg+= "\ngot:      "+str(result)
        self.assertTrue(result==primes, msg)

        primes1 = PyBoolNet.FileExchange.bnet2primes("A, B \n B, !A")
        primes2 = PyBoolNet.FileExchange.bnet2primes("C, B \n D, C")
        self.assertRaises(Exception, PyBoolNet.PrimeImplicants.create_disjoint_union, primes1, primes2)

        
    def test_remove_variables(self):
        primes = PyBoolNet.FileExchange.bnet2primes("A, !C|B \n B, 0 \n C, 1")
        newprimes = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.remove_variables(newprimes,["A","B","C"])
        expected = {}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, newprimes), str(newprimes)+' vs '+str(expected))

        newprimes = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.remove_variables(Primes=primes,Names=[])
        expected = primes
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, newprimes), str(newprimes)+' vs '+str(expected))

        newprimes = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.remove_all_variables_except(Primes=newprimes,Names=["B","C"])
        expected = PyBoolNet.FileExchange.bnet2primes("B, 0 \n C, 1")
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, newprimes), str(newprimes)+' vs '+str(expected))
        
        newprimes = PyBoolNet.PrimeImplicants.copy(primes)
        self.assertRaises(Exception, PyBoolNet.PrimeImplicants.remove_variables, newprimes, ["B"])
        
    def test_create_variables(self):
        primes = PyBoolNet.FileExchange.bnet2primes("v1,v1\nv2,v1")

        answer = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.create_variables(answer, {"v1":"v2"})
        expected = {'v1': [[{'v2': 0}], [{'v2': 1}]], 'v2': [[{'v1': 0}], [{'v1': 1}]]} 
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
        answer = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.create_variables(answer, {"v1":lambda v2: not v2})

        answer = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.create_variables(answer, {"v3":"v2", "v4":lambda v3: v3})

        newprimes = PyBoolNet.PrimeImplicants.copy(primes)
        self.assertRaises(Exception, PyBoolNet.PrimeImplicants.create_variables, newprimes, {"v3":"v4"})
    
    def test_input_combinations(self):
        bnet = "input1, input1 \n input2, input2 \n"
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        expected = [{"input1":0,"input2":0},{"input1":0,"input2":1},{"input1":1,"input2":0},{"input1":1,"input2":1},]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        answer   = list(PyBoolNet.PrimeImplicants.input_combinations(primes))
        answer.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)


        bnet = "v1, v2 \n v2, v1 \n"
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)

        expected = [{}]
        answer   = sorted(PyBoolNet.PrimeImplicants.input_combinations(primes))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    
    def test_copy(self):
        p1 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        p2 = PyBoolNet.PrimeImplicants.copy(p1)
        p2["v1"] = [[{"v1":0}],[{"v1":1}]]
        self.assertFalse(p1==p2)

    def test_find_inputs(self):
        primes = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 1}], [{'C': 0}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        inputs_expected = ['B']
        inputs_returned = PyBoolNet.PrimeImplicants.find_inputs(primes)
        self.assertTrue(inputs_expected == inputs_returned)

    def test_find_constants(self):
        primes = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        constants_expected = {'B':0,'C':1}
        constants_returned = PyBoolNet.PrimeImplicants.find_constants(primes)
        self.assertTrue(constants_expected == constants_returned)

    def test_equal(self):
        p1 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        p2 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v1":1},{"v2":0}],[{"v1":0,"v2":1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(p1,p2))

    def test_percolation(self):
        bnet = "A, 0\nB, A"
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        const = PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
        self.assertTrue(const=={"A":0,"B":0})

        bnet = "A, 0\nB, A"
        primes = PyBoolNet.FileExchange.bnet2primes(bnet)
        const = PyBoolNet.PrimeImplicants.percolate_and_remove_constants(primes)
        self.assertTrue(const=={"A":0,"B":0})
        
    def test_percolation1A(self):
        primes = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_remove_constants(primes)
        expected = {}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation1B(self):
        primes = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
        expected = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{}], []]} # 000
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation2A(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_remove_constants(primes)
        expected = {}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation2B(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
        expected = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[], [{}]]} # 001
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation3A(self):
        primes = {'A': [[{}], []], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_remove_constants(primes)
        expected = {}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation3B(self):
        primes = {'A': [[{}], []], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
        expected = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[], [{}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation4A(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PyBoolNet.PrimeImplicants.percolate_and_remove_constants(primes)
        expected = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_percolation4B(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        expected = PyBoolNet.PrimeImplicants.copy(primes)
        PyBoolNet.PrimeImplicants.percolate_and_keep_constants(primes)
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

    def test_create_blinkers(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PyBoolNet.PrimeImplicants.create_blinkers(Primes=primes, Names=['A'])
        expected = primes = {'A': [[{'A': 1}], [{'A': 0}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected))

class TestFileExchange(unittest.TestCase):
    def test_primes2eqn(self):
        fname_out = os.path.join(FILES_OUT, "fileexchange_primes2eqn.eqn")
        primes = PyBoolNet.Repository.get_primes("raf")
        PyBoolNet.FileExchange.primes2eqn(primes, fname_out)
    
    def test_bnet2primes_operatorbinding(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_operatorbinding.bnet")
        fname_out = os.path.join(FILES_OUT, "fileexchange_operatorbinding.primes")
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
        names = "abcde"
        results = []
        for x in names:
            for y in names:
                name = x
                results.append(PyBoolNet.PrimeImplicants.are_equal({name:primes[x]},{name:primes[y]}))
                                              
        self.assertTrue(all(results))
        
    def test_bnet2primes_results(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_feedback.bnet")
        fname_out = os.path.join(FILES_OUT, "fileexchange_feedback.primes")
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
        primes_expected = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,primes_expected))

    def test_bnet2primes_empty(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_empty.bnet")
        fname_out = os.path.join(FILES_OUT, "fileexchange_empty.primes")
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
        primes_expected = {}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,primes_expected), str(primes))

    def test_bnet2primes_missing_inputs(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_missing_inputs.bnet")
        fname_out = os.path.join(FILES_OUT, "fileexchange_missing_inputs.primes")
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
        primes_expected = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,primes_expected), str(primes))

    def test_bnet2primes_constants(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_constants.bnet")
        fname_out = os.path.join(FILES_OUT, "fileexchange_constants.primes")
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)
        primes_expected = {'A': [[{}], []], 'B': [[], [{}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,primes_expected), str(primes))

    def test_bnet2primes_stdinout(self):
        fname_in  = os.path.join(FILES_IN,  "fileexchange_constants.bnet")
        fname_out1 = os.path.join(FILES_OUT, "fileexchange_stdout1.primes")
        fname_out2 = os.path.join(FILES_OUT, "fileexchange_stdout2.primes")
        file_in = "A, 0\nB, 1"

        expected = {"A":[[{}],[]],"B":[[],[{}]]}
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in)
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,expected), msg)
        
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=file_in)
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,expected), msg)
                                                          
        primes = PyBoolNet.FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out1)
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,expected), msg)

    def test_primes2bnet(self):
        fname = os.path.join(FILES_OUT, "fileexchange_primes2bnet.primes")
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PyBoolNet.FileExchange.primes2bnet(Primes=primes, FnameBNET=fname)
        PyBoolNet.FileExchange.primes2bnet(Primes=primes, FnameBNET=fname, Minimize=True)
        
        # no assertion
        


    def test_read_primes(self):
        fname  = os.path.join(FILES_IN, "fileexchange_missing_inputs.primes")
        
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname)
        primes_expected = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes,primes_expected), str(primes))

    def test_read_write_primes(self):
        fname  = os.path.join(FILES_OUT, "fileexchange_read_write.primes")
        
        primes_write = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PyBoolNet.FileExchange.write_primes(Primes=primes_write, FnamePRIMES=fname)
        primes_read = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname)

        msg = 'wrote primes \n"{p1}" \nbut got \n"{p2}".'.format(p1=str(primes_write), p2=str(primes_read))
        self.assertTrue(PyBoolNet.PrimeImplicants.are_equal(primes_read,primes_write), msg)

    def test_primes2genysis(self):
        fname = os.path.join(FILES_OUT, "fileexchange_primes2genysis.genysis")
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PyBoolNet.FileExchange.primes2genysis(Primes=primes, FnameGENYSIS=fname)
        ## no assertion ##

    def test_primes2bns(self):
        fname = os.path.join(FILES_OUT, "fileexchange_primes2bns.bns")
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PyBoolNet.FileExchange.primes2bns(Primes=primes, FnameBNS=fname)
        ## no assertion ##

    def test_primes2smv(self):
        primes = {'vB': [[{}], []], 'vC': [[{'vC': 0}], [{'vC': 1}]], 'vA': [[{'vB': 0, 'vC': 1}], [{'vC': 0}, {'vB': 1}]]}

        fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_syn.smv")
        PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="synchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_async.smv")
        PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="asynchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        fname = os.path.join(FILES_OUT, "fileexchange_primes2smv_mixed.smv")
        PyBoolNet.ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="mixed", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        ## no assertion ##

    def test_primes2asp(self):
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        
        for i, (cbounds, cproj) in enumerate(itertools.product([None,(1,2)],[None,['A','B']])):
            fname = os.path.join(FILES_OUT, "fileexchange_primes2asp_case%i.asp"%i)
            PyBoolNet.TrapSpaces.primes2asp(Primes=primes, FnameASP=fname, Bounds=cbounds, Project=cproj, InsideOf={}, OutsideOf={})
        ## no assertion ##


class TestInteractionGraphs(unittest.TestCase):

    def test_find_minimal_autonomous_nodes(self):
        primes = PyBoolNet.Repository.get_primes("randomnet_n15k3")
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(primes)
        nodes = PyBoolNet.InteractionGraphs.find_minimal_autonomous_nodes(igraph)
        expected = [set(['Gene8', 'Gene9', 'Gene1', 'Gene2', 'Gene3', 'Gene4', 'Gene5', 'Gene6', 'Gene7', 'Gene12', 'Gene13', 'Gene10', 'Gene11', 'Gene14'])]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(nodes)
        self.assertTrue( expected==nodes , msg)
        
    def test_create_image(self):
        fname = os.path.join(FILES_OUT, "interactiongraphs_create_image.pdf")
        primes = PyBoolNet.Repository.get_primes("raf")
        PyBoolNet.InteractionGraphs.create_image(primes, fname)

    def test_outdag(self):
        igraph = networkx.DiGraph()
        igraph.add_edges_from([(1,1),(2,1),(2,3),(3,2),(2,4),(4,1),(4,5),(5,6),(6,6),(5,7)])
        outdag = PyBoolNet.InteractionGraphs.find_outdag(igraph)
        msg = "\nexpected: "+str([7])
        msg+= "\ngot:      "+str(outdag)
        self.assertTrue(outdag == [7], msg)
                              

    def test_activities2animation(self):
        fname_in  = os.path.join(FILES_IN,  "irma.primes")
        fname_out1 = os.path.join(FILES_OUT, "irma*.png")
        fname_out2 = os.path.join(FILES_OUT, "irma.gif")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(primes)
        
        activities = [{"gal":0, "Cbf1":1, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":1, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":1, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":1, "Swi5":0},
                      ]

        PyBoolNet.InteractionGraphs.activities2animation(IGraph=igraph, Activities=activities, FnameTMP=fname_out1, FnameGIF=fname_out2)
        # no assertion

    def test_primes2igraph1(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        nodes_edges = sorted(igraph.nodes()) + sorted(igraph.edges())
        expected =  ['Ash1', 'Cbf1', 'Gal4', 'Gal80', 'Swi5', 'gal',
                     ('Ash1', 'Cbf1'), ('Cbf1', 'Ash1'), ('Gal4', 'Swi5'), ('Gal80', 'Gal4'),
                     ('Swi5', 'Gal4'), ('gal', 'Ash1'), ('gal', 'Gal80'), ('gal', 'gal')]

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(sorted(igraph.nodes()) + sorted(igraph.edges()))
        self.assertTrue(nodes_edges == expected, msg)

    def test_primes2igraph2(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('Ash1', {}), ('Cbf1', {}), ('Gal4', {}), ('Gal80', {}), ('Swi5', {}), ('gal', {}),
                     ('Ash1', 'Cbf1', {'sign': {1}}), ('Cbf1', 'Ash1', {'sign': {1}}), ('Gal4', 'Swi5', {'sign': {-1}}),
                     ('Gal80', 'Gal4', {'sign': {1}}), ('Swi5', 'Gal4', {'sign': {-1}}), ('gal', 'Ash1', {'sign': {1}}),
                     ('gal', 'Gal80', {'sign': {-1}}), ('gal', 'gal', {'sign': {1}})]

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)))
        self.assertTrue(nodes_edges == expected, msg)

    def test_primes2igraph3(self):
        primes = {'A': [[{'A':0}], [{'A':1}]], 'B': [[{}], []], 'C': [[{'B': 0}], [{'B': 1}]]}
                  
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('A', {}), ('B', {}), ('C', {}),
                     ('A', 'A', {'sign': {1}}), ('B', 'C', {'sign': {1}})]
        self.assertTrue(nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)))

    def test_primes2igraph3(self):
        primes = {'A': [[{}],[]], 'B': [[{'B':0}],[{'B':1}]], 'C': [[{'C':1}],[{'C':0}]], 'D': [[{'B':0,'C':0},{'B':1,'C':1}],
                                                                                                [{'B':1,'C':0},{'B':0,'C':1}]]}
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('A', {}), ('B', {}), ('C', {}), ('D', {}), ('B', 'B', {'sign': {1}}),
                     ('B', 'D', {'sign': {1, -1}}), ('C', 'C', {'sign': {-1}}), ('C', 'D', {'sign': {1, -1}})]
        self.assertTrue(nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)))

    def test_igraph2dot(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
        fname_out = os.path.join(FILES_OUT, "interactiongraphs_igraph2dot.dot")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out)
        ## no assertion ##

    def test_igraph2dot_string(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=None)
        ## no assertion ##

    def test_igraph2image(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_irma.primes")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        fname_out = os.path.join(FILES_OUT, "interactiongraphs_igraph2image.jpg")
        PyBoolNet.InteractionGraphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out)
        ## no assertion ##

    def test_dot2image(self):
        fname_in = os.path.join(FILES_IN, "interactiongraphs_topology.dot")
        fname_out1 = os.path.join(FILES_OUT, "interactiongraphs_dot2image1.jpg")
        fname_out2 = os.path.join(FILES_OUT, "interactiongraphs_dot2image2.svg")
        fname_out3 = os.path.join(FILES_OUT, "interactiongraphs_dot2image3.eps")
        fname_out4 = os.path.join(FILES_OUT, "interactiongraphs_dot2image4.gif")
        
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out1)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out2)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out3)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_in, FnameIMAGE=fname_out4)
        ## no assertion ##    

    def test_styles(self):
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
        fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_interactionsigns.dot")
        fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_interactionsigns.pdf")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        PyBoolNet.InteractionGraphs.add_style_interactionsigns(IGraph=igraph)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
        PyBoolNet.InteractionGraphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

        fname_in  = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
        fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_activities.dot")
        fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_activities.pdf")

        PyBoolNet.InteractionGraphs.add_style_interactionsigns(IGraph=igraph)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
        PyBoolNet.InteractionGraphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        activities = {'v1':1,'v2':0,'v3':1,'v4':1,'v5':1,'v6':0}
        PyBoolNet.InteractionGraphs.add_style_activities(IGraph=igraph, Activities=activities)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)
        
        fname_in  = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
        fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_sccs.dot")
        fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_sccs.pdf")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        PyBoolNet.InteractionGraphs.add_style_sccs(IGraph=igraph)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)

        fname_in  = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
        fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_ioc.pdf")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        PyBoolNet.InteractionGraphs.add_style_inputs(IGraph=igraph)
        PyBoolNet.InteractionGraphs.add_style_constants(IGraph=igraph)
        PyBoolNet.InteractionGraphs.add_style_outputs(IGraph=igraph)
        PyBoolNet.InteractionGraphs.igraph2image(IGraph=igraph, FnameIMAGE=fname_out_pdf)

        fname_in  = os.path.join(FILES_IN, "interactiongraphs_topology.primes")
        fname_out_pdf = os.path.join(FILES_OUT, "interactiongraphs_style_subgrapghs.pdf")
        fname_out_dot = os.path.join(FILES_OUT, "interactiongraphs_style_subgrapghs.dot")
        primes = PyBoolNet.FileExchange.read_primes(FnamePRIMES=fname_in)
        
        igraph = PyBoolNet.InteractionGraphs.primes2igraph(Primes=primes)
        subgraphs = [(["v1","v2"],{}),(["v3","v4"],{"label":"jo"})]
        PyBoolNet.InteractionGraphs.add_style_subgraphs(IGraph=igraph, Subgraphs=subgraphs)
        PyBoolNet.InteractionGraphs.igraph2dot(IGraph=igraph, FnameDOT=fname_out_dot)
        PyBoolNet.InteractionGraphs.dot2image(FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf)

        ## no assertion ##

    



if __name__=="__main__":


    
    if 1:
        # run all tests
        unittest.main(verbosity=2, buffer=True)

    if 0:
        # run single test
        suite = unittest.TestSuite()
        suite.addTest(TestAttractorDetection("test_attractor_representatives"))
        
        runner = unittest.TextTestRunner(buffer=True)
        runner.run(suite)

    if 0:
        # run test class

        import inspect

        class_name = TestPyBoolNet.PrimeImplicants

        suite = unittest.TestSuite()
        for name, obj in inspect.getmembers(class_name):
            if name.startswith("test_"):
                suite.addTest(class_name(name))

        runner = unittest.TextTestRunner()
        runner.run(suite)
            
            
        
            
    







