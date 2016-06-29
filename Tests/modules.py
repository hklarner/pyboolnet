

import unittest
import os
import sys
import subprocess
import networkx
import itertools

BASE = os.path.normpath(os.path.abspath(os.path.join(os.path.dirname(__file__), "..")))
sys.path.append(BASE)

import FileExchange
import PrimeImplicants
import InteractionGraphs
import StateTransitionGraphs
import TrapSpaces
import ModelChecking
import AttractorDetection
import TemporalQueries
import QuineMcCluskey
import Examples
import Utility

FILES_IN   = os.path.join(BASE, "Tests", "Files", "Input")
FILES_OUT  = os.path.join(BASE, "Tests", "Files")
config = Utility.Miscellaneous.myconfigparser.SafeConfigParser()
config.read( os.path.join(BASE, "Dependencies", "settings.cfg") )


def run():
    unittest.main(verbosity=2, buffer=True, exit=False, module=__name__)


def update_input_files():
    return
    fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.bnet" )
    fname_out_primes = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
    fname_out_dot = os.path.join( FILES_IN, "interactiongraphs_topology.dot" )
    primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out_primes )
    igraph = InteractionGraphs.primes2igraph( Primes=primes )
    InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )

    # convert .bnet files to .primes files
    for name in ['trapspaces_tsfree','trapspaces_posfeedback']:
        fname_in  = os.path.join( FILES_IN, name+".bnet" )
        fname_out_primes = os.path.join( FILES_IN, name+".primes" )
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out_primes )


class TestQuineMcCluskey(unittest.TestCase):
    def test_functions2mindnf(self):
        bfunctions = {'v1': lambda v1,v2: v1 or not v2, 'v2': lambda v1: not v1,
                      'v3': lambda : False, 'v4': lambda v3: v3 or not v3}

        answer = QuineMcCluskey.functions2mindnf(bfunctions)
        expected = {'v1': '((! v2) | v1)', 'v2': '(! v1)', 'v3': '0', 'v4': '1'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    def test_primes2mindnf(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}

        answer = QuineMcCluskey.primes2mindnf(primes)
        expected = {'A': '0', 'C': '(B & (! A))', 'B': '1'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        

class TestStateTransitionGraphs(unittest.TestCase):
    def test_random_mixed_transition(self):
        fname_in  = os.path.join( FILES_IN,  "randomnet.bnet" )
        fname_out = os.path.join( FILES_OUT, "randomnet.primes" )
        primes = FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        StateTransitionGraphs.random_successor_mixed( primes, state )
        # no assertion

        
    def test_successors_asynchronous(self):
        fname_in  = os.path.join( FILES_IN,  "randomnet.bnet" )
        fname_out = os.path.join( FILES_OUT, "randomnet.primes" )
        primes = FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        StateTransitionGraphs.successors_asynchronous( primes, state )
        # no assertion
        
    def test_successor_synchronous(self):
        fname_in  = os.path.join( FILES_IN,  "randomnet.bnet" )
        fname_out = os.path.join( FILES_OUT, "randomnet.primes" )
        primes = FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        state = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        StateTransitionGraphs.successor_synchronous( primes, state )
        # no assertion


    def test_best_first_reachability(self):
        fname_in  = os.path.join( FILES_IN,  "randomnet.bnet" )
        fname_out = os.path.join( FILES_OUT, "randomnet.primes" )
        primes = FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        initialspace = dict([('Gene%i'%(i+1),i%2) for i in range(20)])
        goalspace = {'Gene2':0,'Gene4':0,'Gene6':0,'Gene8':0}
        memory = 10000
        path = StateTransitionGraphs.best_first_reachability( primes, initialspace, goalspace, memory )
        self.assertTrue(path!=None)

    def test_state2str(self):
        state = {"v2":0, "v1":1, "v3":1}
        
        answer = StateTransitionGraphs.state2str(state)
        expected = "101"
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

    def test_primes2stg(self):
        fname_in  = os.path.join( FILES_IN,  "irma.primes" )
        fname_out = os.path.join( FILES_OUT, "irma_stg.pdf" )

        primes = FileExchange.read_primes(FnamePRIMES=fname_in)

        init = lambda x: x["Cbf1"]+x["Ash1"]+x["Gal80"]==1

        StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous", InitialStates=init)
        StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)

        init = []
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = stg.nodes()
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        init = ["000010"]
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = sorted(stg.nodes())
        expected = ['000010', '000110']
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)


        init = [{'Cbf1':0, 'Gal4':1, 'Gal80':0, 'gal':1, 'Swi5':0, 'Ash1':1}]
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous", InitialStates=init)
        answer = sorted(stg.nodes())
        expected = ['010001', '010011', '100011', '101001']
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
    def test_stg2dot(self):
        fname_in  = os.path.join( FILES_IN,  "irma.primes" )
        fname_out = os.path.join( FILES_OUT, "irma_stg.dot" )

        primes = FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.stg2dot(stg, fname_out)
        # no assertion

    def test_stg2image(self):
        fname_in  = os.path.join( FILES_IN,  "irma.primes" )
        fname_out1 = os.path.join( FILES_OUT, "irma_stg_async.pdf" )
        fname_out2 = os.path.join( FILES_OUT, "irma_stg_tendencies_async.pdf" )
        fname_out3 = os.path.join( FILES_OUT, "irma_stg_sccs_async.pdf" )

        primes = FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.stg2image(stg, fname_out1)

        StateTransitionGraphs.add_style_tendencies(stg)
        StateTransitionGraphs.stg2image(stg, fname_out2)

        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.add_style_sccs(stg)
        StateTransitionGraphs.stg2image(stg, fname_out3)

        fname_out1 = os.path.join( FILES_OUT, "irma_stg_sync.pdf" )
        fname_out2 = os.path.join( FILES_OUT, "irma_stg_tendencies_sync.pdf" )
        fname_out3 = os.path.join( FILES_OUT, "irma_stg_sccs_sync.pdf" )
        fname_out4 = os.path.join( FILES_OUT, "irma_stg_path.pdf" )

        primes = FileExchange.read_primes(FnamePRIMES=fname_in)
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        StateTransitionGraphs.stg2image(stg, fname_out1)

        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.add_style_tendencies(stg)
        StateTransitionGraphs.stg2image(stg, fname_out2)

        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="synchronous")
        StateTransitionGraphs.add_style_sccs(stg)
        StateTransitionGraphs.stg2image(stg, fname_out3)


        init = StateTransitionGraphs.random_state( Primes=primes )
        walk = StateTransitionGraphs.random_walk( Primes=primes, Update="asynchronous", InitialState=init, Length=5 )
        stg = StateTransitionGraphs.primes2stg(Primes=primes, Update="asynchronous")
        StateTransitionGraphs.add_style_path(stg, walk, "red")
        init = StateTransitionGraphs.random_state( Primes=primes )
        walk = StateTransitionGraphs.random_walk( Primes=primes, Update="asynchronous", InitialState=init, Length=5 )
        StateTransitionGraphs.add_style_path(stg, walk, "blue")
        StateTransitionGraphs.stg2image(stg, fname_out4)
        # no assertion
        
        
    def test_random_state(self):
        fname_in  = os.path.join( FILES_IN,  "irma.primes" )
        primes = FileExchange.read_primes(FnamePRIMES=fname_in)
        StateTransitionGraphs.random_state( Primes=primes )
        StateTransitionGraphs.random_state( Primes=primes, Subspace="111-0-" )
        # no assertion

    def test_stg2sccgraph(self):
        fname_out = os.path.join( FILES_OUT, "raf_sccgraph.pdf" )
        primes = Examples.get_primes("raf")
        stg = StateTransitionGraphs.primes2stg(primes, "asynchronous")
        sccg = StateTransitionGraphs.stg2sccgraph(stg)
        StateTransitionGraphs.sccgraph2image(sccg, fname_out)
        # no assertion

    def test_stg2condensationgraph(self):
        fname_out = os.path.join( FILES_OUT, "raf_cgraph.pdf" )
        primes = Examples.get_primes("raf")
        stg = StateTransitionGraphs.primes2stg(primes, "asynchronous")
        cgraph = StateTransitionGraphs.stg2condensationgraph(stg)
        StateTransitionGraphs.condensationgraph2image(cgraph, fname_out)
        # no assertion

    def test_stg2htg(self):
        fname_out = os.path.join( FILES_OUT, "raf_htg.pdf" )
        primes = Examples.get_primes("raf")
        stg = StateTransitionGraphs.primes2stg(primes, "asynchronous")
        htg = StateTransitionGraphs.stg2htg(stg)
        StateTransitionGraphs.htg2image(htg, fname_out)
        # no assertion
        



class TestAttractorDetection(unittest.TestCase):
    def test_compute_attractors_tarjan(self):
        bnet = ["x, !x&y | z",
                "y, !x | !z",
                "z, x&!y"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)
        stg = StateTransitionGraphs.primes2stg(primes, "asynchronous")
        attractors = AttractorDetection.compute_attractors_tarjan(primes, stg)

    
        answer = []
        for A in attractors:
            answer.append([StateTransitionGraphs.state2str(x) for x in A])
        answer   = sorted(answer)
        expected = sorted([["101"], ["010","110"]])
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        
        self.assertTrue(answer==expected, msg)
        
    def test_find_attractor_by_randomwalk_and_ctl(self):
        fname_in  = os.path.join( FILES_IN,  "randomnet.bnet" )
        fname_out = os.path.join( FILES_OUT, "randomnet.primes" )
        primes = FileExchange.bnet2primes(BNET=fname_in, FnamePRIMES=fname_out)

        subspace = {'Gene1':0,'Gene3':0,'Gene5':0,'Gene7':0,'Gene9':0}
        lengthrandomwalk = 200
        attempts = 10
        update = "asynchronous"
        AttractorDetection.find_attractor_by_randomwalk_and_ctl( primes, update, subspace, lengthrandomwalk, attempts )
        update = "synchronous"
        AttractorDetection.find_attractor_by_randomwalk_and_ctl( primes, update, subspace, lengthrandomwalk, attempts )
        update = "mixed"
        AttractorDetection.find_attractor_by_randomwalk_and_ctl( primes, update, subspace, lengthrandomwalk, attempts )
        # no assertion
        
    def test_univocal(self):

        # not univocal
        bnet= ["v1, !v1&!v2 | v2&!v3",
               "v2, v1&v2",
               "v3, v2 | v3",
               "v4, 1"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        trapspace = {"v4":1}
        answer, state1, state2 = AttractorDetection.univocal( primes, "asynchronous", trapspace )
        expected = False
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        trapspace = {}
        answer, state1, state2 = AttractorDetection.univocal( primes, "asynchronous", trapspace )
        expected = (4,4)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str((len(state1), len(state2)))
        self.assertTrue((len(state1), len(state2))==expected, msg)


        # univocal with unique steady state

        bnet= ["v1, !v1&!v2 | !v3",
               "v2, v1&v2",
               "v3, v1&v3 | v2",
               "v4, 0"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        trapspace = {}
        answer = AttractorDetection.univocal( primes, "asynchronous", trapspace )
        expected = (True, {"v1":1,"v2":0,"v3":0,"v4":0}, None)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        

    def test_faithful(self):
        pass


        bnet = ["v1, !v1&!v2 | !v2&!v3",
                "v2, !v1&!v2&v3 | v1&!v3",
                "v3, !v1&v3 | !v2"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        # not faithful
        trapspace = {}
        answer, state = AttractorDetection.faithful( primes, "asynchronous", trapspace )
        expected = False
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        # faithful
        trapspace = {"v3":1}
        answer, state = AttractorDetection.faithful( primes, "asynchronous", trapspace )
        expected = True
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        
    def test_completeness_naive(self):
        
        bnet= ["v1, v1 | v2&!v3",
               "v2, !v1&v2&v3",
               "v3, !v2&!v3 | v2&v3"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        # not complete
        subspaces = ["00-","10-"]
        expected  = False
        answer, counterex = AttractorDetection.completeness_naive( primes, "asynchronous", subspaces )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)


        # complete
        subspaces = ["00-","10-", {"v1":0,"v2":1,"v3":1}]
        expected  = True
        answer, counterex = AttractorDetection.completeness_naive( primes, "asynchronous", subspaces )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)



    def test_completeness_iterative(self):
        
        bnet= ["v1, !v1&v2&v3 | v1&!v2&!v3",
               "v2, !v1&!v2 | v1&v3",
               "v3, !v1&v3 | v1&v2"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        # not complete
        expected  = False
        answer, counterex = AttractorDetection.completeness_iterative( primes, "asynchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        # complete
        expected = True
        answer, counterex = AttractorDetection.completeness_iterative( primes, "synchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)
        
        bnet = ["v1, !v1&v2&v3 | v1&!v2&!v3",
                "v2, !v1&!v2 | v1&v3",
                "v3, v2 | v3"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        # complete
        expected = True
        answer, counterex = AttractorDetection.completeness_iterative( primes, "asynchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        answer, counterex = AttractorDetection.completeness_iterative( primes, "synchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        bnet = ["v0,   v0",
                "v1,   v2",
                "v2,   v1",
                "v3,   v1&v0",
                "v4,   v2",
                "v5,   v3&!v6",
                "v6,   v4&v5"]
        bnet = "\n".join(bnet)
        primes = FileExchange.bnet2primes(bnet)

        expected = True
        answer, counterex = AttractorDetection.completeness_iterative( primes, "asynchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

        expected = False
        answer, counterex = AttractorDetection.completeness_iterative( primes, "synchronous" )
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
        primes = FileExchange.bnet2primes(bnet)
        expected = True
        answer, counterex = AttractorDetection.completeness_iterative( primes, "synchronous" )
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue(answer==expected, msg)

class TestTemporalQueries(unittest.TestCase):
    def test_EF_subspaces(self):
        subspaces = [{'v1':0,'v2':0}, {'v1':1,'v2':1}]
        names = ["v1","v2"]
        expected  = 'EF(!v1&!v2 | v1&v2)'
        query = TemporalQueries.EF_oneof_subspaces(names, subspaces)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(query)
        self.assertTrue(query==expected, msg)

    def EF_unsteady(self):
        names = ['v1','v2','v3']
        expected  = 'EF(v1_unsteady) & EF(v2_unsteady) & EF(v3_unsteady)'
        query = TemporalQueries.EF_unsteady_states(names)
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(query)
        self.assertTrue(query==expected, msg)

    def test_AGEF_subspaces(self):
        subspaces = [{'v1':0,'v2':0},{'v2':1}]
        names = ["v1","v2"]
        expected  = 'AG(EF(!v1&!v2 | v2))'
        query = TemporalQueries.AGEF_oneof_subspaces(names, subspaces)
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

        fname_out = os.path.join( FILES_OUT, "modelchecking_acceptingstates.smv" )
        primes = FileExchange.bnet2primes(bnet)
        
        spec = "CTLSPEC EF(!Erk&!Mek&Raf) &  EF(Erk&Mek&Raf)"
        init = "INIT TRUE"
        update = "asynchronous"

        ModelChecking.primes2smv(primes, update, init, spec, fname_out)
        answer, accepting = ModelChecking.check_smv(fname_out, AcceptingStates=True)

        expected = {'ACCEPTING_SIZE': 3, 'INIT': 'TRUE', 'INIT_SIZE': 8, 'INITACCEPTING_SIZE': 3, 'INITACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))', 'ACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(accepting)
        self.assertTrue( accepting==expected, msg )

        answer, accepting = ModelChecking.check_primes(primes, update, init, spec, AcceptingStates=True)
        expected = {'ACCEPTING_SIZE': 3, 'INIT': 'TRUE', 'INIT_SIZE': 8, 'INITACCEPTING_SIZE': 3, 'INITACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))', 'ACCEPTING': '!(Erk & (Mek) | !Erk & ((Raf) | !Mek))'}
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(accepting)
        self.assertTrue( accepting==expected, msg )
        
        
    def test_check_smv_true(self):
        fname_in  = os.path.join( FILES_IN,  "modelchecking_check_smv_true.smv" )

        self.assertTrue(ModelChecking.check_smv(FnameSMV=fname_in, DisableCounterExamples=True,
                                                DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True))
        
    def test_check_smv_false(self):
        fname_in  = os.path.join( FILES_IN,  "modelchecking_check_smv_false.smv" )

        self.assertFalse(ModelChecking.check_smv(FnameSMV=fname_in, DisableCounterExamples=True,
                                                DynamicReorder=True, DisableReachableStates=True, ConeOfInfluence=True))
        

    def test_check_smv_counterexample(self):
        fname_in  = os.path.join( FILES_IN,  "modelchecking_check_smv_counterexample.smv" )

        answer, counterex = ModelChecking.check_smv(FnameSMV=fname_in, DisableCounterExamples=False, DynamicReorder=True,
                                                    DisableReachableStates=True, ConeOfInfluence=True)


        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})
        
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue( counterex==expected, msg )
        

    def test_check_primes_async(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}
        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})

        answer, counterex = ModelChecking.check_primes( Primes=primes, Update="asynchronous", InitialStates="INIT !v1&v2&!v3",
                                                        Specification="CTLSPEC AF(!v1&!v2&v3)", DisableCounterExamples=False,
                                                        DynamicReorder=True, DisableReachableStates=False, ConeOfInfluence=True )

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue( counterex==expected, msg )
        

    def test_check_primes_sync(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}
        

        expected = None
        
        answer, counterex = ModelChecking.check_primes( Primes=primes, Update="synchronous", InitialStates="INIT !v1&v2&!v3",
                                                        Specification="CTLSPEC AF(!v1&!v2&v3)", DisableCounterExamples=False,
                                                        DynamicReorder=True, DisableReachableStates=False, ConeOfInfluence=True )

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue( counterex==expected, msg )
        

    def test_check_primes_mixed(self):
        primes = {'v1': [[{'v1': 0, 'v3': 1}, {'v1': 0, 'v2': 1}], [{'v2': 0, 'v3': 0}, {'v1': 1}]], 'v2': [[{'v3': 1}, {'v1': 0}], [{'v1': 1, 'v3': 0}]], 'v3': [[{'v1': 1, 'v2': 0, 'v3': 0}], [{'v3': 1}, {'v2': 1}, {'v1': 0}]]}


        expected = ({'v1':0,'v2':1,'v3':0},{'v1':0,'v2':0,'v3':0},{'v1':1,'v2':0,'v3':0},
                    {'v1':1,'v2':1,'v3':0},{'v1':1,'v2':1,'v3':1},{'v1':1,'v2':0,'v3':1})

        answer, counterex = ModelChecking.check_primes( Primes=primes, Update="mixed", InitialStates="INIT !v1&v2&!v3",
                                                        Specification="CTLSPEC AF(!v1&!v2&v3)", DisableCounterExamples=False,
                                                        DynamicReorder=True, DisableReachableStates=False, ConeOfInfluence=True )        

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(counterex)
        self.assertTrue( counterex==expected, msg )


class TestTrapSpaces(unittest.TestCase):
    def test_trap_spaces_piped1(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="min" )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )
        

    def test_trap_spaces_piped2(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_tsfree.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="min" )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )
        
        
    def test_trap_spaces_tsfree(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_tsfree.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_tsfree_min.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="min", FnameASP=fname_out )
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )        

        fname_in  = os.path.join( FILES_IN,  "trapspaces_tsfree.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_tsfree_all.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="all", FnameASP=fname_out )
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

        fname_in  = os.path.join( FILES_IN,  "trapspaces_tsfree.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_tsfree_max.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="max", FnameASP=fname_out )
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

        
    def test_trap_spaces_posfeedback_min(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_posfeedback_min.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="min", FnameASP=fname_out )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

    def test_trap_spaces_posfeedback_max(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_posfeedback_max.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="max", FnameASP=fname_out )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

    def test_trap_spaces_posfeedback_all(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_posfeedback_all.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces( Primes=primes, Type="all", FnameASP=fname_out )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{},{'v1': 0, 'v2': 0, 'v3': 0}, {'v1': 1, 'v2': 1, 'v3': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

    def test_trap_spaces_posfeedback_bounds1(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_posfeedback_bounds1.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces_bounded( Primes=primes, Type="all", Bounds=(1,2), FnameASP=fname_out )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = []
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

    def test_trap_spaces_posfeedback_bounds2(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_posfeedback.primes" )
        fname_out = os.path.join( FILES_OUT, "trapspaces_posfeedback_bounds2.asp" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )

        tspaces = TrapSpaces.trap_spaces_bounded( Primes=primes, Type="max", Bounds=(0,100), FnameASP=fname_out )
        tspaces.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces)
        self.assertTrue( tspaces==expected, msg )

    def test_trap_spaces_bounded(self):
        fname_in  = os.path.join( FILES_IN,  "trapspaces_bounded.bnet" )
        fname_out  = os.path.join( FILES_IN,  "trapspaces_bounded.primes" )
        primes = FileExchange.bnet2primes(fname_in, fname_out)

        tspaces_all = TrapSpaces.trap_spaces(primes, "all")
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
        self.assertTrue( tspaces_all==expected, msg )
        
        tspaces_min = TrapSpaces.trap_spaces(primes, "min")
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
        self.assertTrue( tspaces_min==expected, msg )

        
        tspaces_max = TrapSpaces.trap_spaces(primes, "max")
        tspaces_max.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"v3":1},
                    {"v3":0},
                    {"v1":1},
                    {"v1":0,"v2":0},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_max)
        self.assertTrue( tspaces_max==expected, msg )

        tspaces_bounded = TrapSpaces.trap_spaces_bounded(primes, "max", Bounds=(1,1))
        tspaces_bounded.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"v3":1},
                    {"v3":0},
                    {"v1":1},
                    ]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(tspaces_bounded)
        self.assertTrue( tspaces_bounded==expected, msg )

        tspaces_bounded = TrapSpaces.trap_spaces_bounded(primes, "max", Bounds=(2,3))
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
        self.assertTrue( tspaces_bounded==expected, msg )

        tspaces_bounded = TrapSpaces.trap_spaces_bounded(primes, "all", Bounds=(2,3))
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
        self.assertTrue( tspaces_bounded==expected, msg )


        tspaces_bounded = TrapSpaces.trap_spaces_bounded(primes, "min", Bounds=(2,3))
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
        self.assertTrue( tspaces_bounded==expected, msg )


    def test_steady_states_projected(self):
        lines = ["x,    !x&!y | x&y",
                 "y,    y",
                 "z,    z"]
        bnet = "\n".join(lines)
        primes = FileExchange.bnet2primes(bnet)

        # network has 4 steady states: 010,110,011,111

        result = TrapSpaces.steady_states_projected(primes, ["y"], Aggregate=True)
        expected = [({"y":1},4)]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )

        result = TrapSpaces.steady_states_projected(primes, ["y","x"], Aggregate=False)
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{"x":0, "y":1}, {"x":1, "y":1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )


    def test_trap_spaces_inside_and_outside(self):
        lines = ["x,    !x&!y | x&y",
                 "y,    y",
                 "z,    z"]
        bnet = "\n".join(lines)
        primes = FileExchange.bnet2primes(bnet)

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

        result = TrapSpaces.trap_spaces_outsideof(primes, "all", OutsideOf={'y': 0, 'z': 1})
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}, {'y': 0}, {'y': 0, 'z': 1}, {'z': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )

        result = TrapSpaces.trap_spaces_insideof(primes, "all", InsideOf={'y': 1, 'x': 0})
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'y': 1, 'x': 0}, {'y': 1, 'x': 0, 'z': 0}, {'y': 1, 'x': 0, 'z': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )


    def test_encoding_bijection(self):
        """
        The mapping from stable and consistent prime implicant sets to trap spaces is surjective but not injective.
        Two different arc sets may lead to the same trap space.
        In the following example there are four trap stable+consistent arc sets but only two trap spaces.
        """

        bnet = "\n".join(["v1,v1|v2","v2,v1"])
        primes = FileExchange.bnet2primes(bnet)

        result = TrapSpaces.trap_spaces(primes, "all")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{}, {'v1': 0, 'v2': 0}, {'v1': 1}, {'v1': 1, 'v2': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )
        
        result = TrapSpaces.trap_spaces(primes, "min")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0}, {'v1': 1, 'v2': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )
        
        result = TrapSpaces.trap_spaces(primes, "max")
        result.sort(key=lambda x: tuple(sorted(x.items())))
        expected = [{'v1': 0, 'v2': 0}, {'v1': 1}]
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(result)
        self.assertTrue( result==expected, msg )
        
        
        

class TestPrimeImplicants(unittest.TestCase):
    def test_input_combinations(self):
        bnet = "input1, input1 \n input2, input2 \n"
        primes = FileExchange.bnet2primes(bnet)

        expected = [{"input1":0,"input2":0},{"input1":0,"input2":1},{"input1":1,"input2":0},{"input1":1,"input2":1},]
        expected.sort(key=lambda x: tuple(sorted(x.items())))
        answer   = list(PrimeImplicants.input_combinations(primes))
        answer.sort(key=lambda x: tuple(sorted(x.items())))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue( answer==expected, msg )


        bnet = "input1, input2 \n input2, input1 \n"
        primes = FileExchange.bnet2primes(bnet)

        expected = []
        answer   = sorted(PrimeImplicants.input_combinations(primes))
        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(answer)
        self.assertTrue( answer==expected, msg )

    
    def test_copy(self):
        p1 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        p2 = PrimeImplicants.copy(p1)
        p2["v1"] = [[{"v1":0}],[{"v1":1}]]
        self.assertFalse( p1==p2 )

    def test_find_inputs(self):
        primes = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 1}], [{'C': 0}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        inputs_expected = ['B']
        inputs_returned = PrimeImplicants.find_inputs(primes)
        self.assertTrue( inputs_expected == inputs_returned )

    def test_find_constants(self):
        primes = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        constants_expected = {'B':0,'C':1}
        constants_returned = PrimeImplicants.find_constants(primes)
        self.assertTrue( constants_expected == constants_returned )

    def test_equal(self):
        p1 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        p2 = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v1":1},{"v2":0}],[{"v1":0,"v2":1}]]}
        self.assertTrue( PrimeImplicants.are_equal(p1,p2) )

    def test_remove_variables(self):
        primes = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PrimeImplicants.remove_variables(Primes=primes,Names=list(primes.keys()))
        expected = {}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

        primes   = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PrimeImplicants.remove_variables(Primes=primes,Names=[])
        expected = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

        primes = {'B': [[{}], []], 'C': [[], [{}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        PrimeImplicants.remove_variables(Primes=primes,Names=['B','C'])
        expected = {'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation(self):
        bnet = "A, 0\nB, A"
        primes = FileExchange.bnet2primes(bnet)
        const = PrimeImplicants.percolate_constants(primes)
        self.assertTrue( const=={"A":0,"B":0} )
        
    def test_percolation1A(self):
        primes = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=True)
        expected = {}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation1B(self):
        primes = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=False)
        expected = {'A': [[{}], []], 'B': [[{}], []], 'C': [[{}], []]} # 000
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation2A(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=True)
        expected = {}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation2B(self):
        primes = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[{'A': 1}, {'B': 0}], [{'A': 0, 'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=False)
        expected = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[], [{}]]} # 001
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation3A(self):
        primes = {'A': [[{}], []], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=True)
        expected = {}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation3B(self):
        primes = {'A': [[{}], []], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=False)
        expected = {'A': [[{}], []], 'B': [[], [{}]], 'C': [[], [{}]]}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation4A(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=True)
        expected = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_percolation4B(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        expected = PrimeImplicants.copy(primes)
        PrimeImplicants.percolate_constants(Primes=primes,RemoveConstants=False)
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

    def test_create_blinkers(self):
        primes = {'A': [[{'A': 0}], [{'A': 1}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        PrimeImplicants.create_blinkers(Primes=primes, Names=['A'])
        expected = primes = {'A': [[{'A': 1}], [{'A': 0}]], 'B': [[{'A': 1}], [{'A': 0}]], 'C':[[{'B': 0}], [{'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(expected, primes), str(primes)+' vs '+str(expected) )

class TestFileExchange(unittest.TestCase):
    def test_bnet2primes_operatorbinding(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_operatorbinding.bnet" )
        fname_out = os.path.join( FILES_OUT, "fileexchange_operatorbinding.primes" )
        
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out )
        names = "abcde"
        results = []
        for x in names:
            for y in names:
                name = x
                results.append( PrimeImplicants.are_equal({name:primes[x]},{name:primes[y]}) )
                                              
        self.assertTrue( all(results) )
        
    def test_bnet2primes_results(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_feedback.bnet" )
        fname_out = os.path.join( FILES_OUT, "fileexchange_feedback.primes" )
        
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out )
        primes_expected = {"v1":[[{"v2":0}],[{"v2":1}]],"v2":[[{"v2":0},{"v1":1}],[{"v1":0,"v2":1}]]}
        self.assertTrue( PrimeImplicants.are_equal(primes,primes_expected) )

    def test_bnet2primes_empty(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_empty.bnet" )
        fname_out = os.path.join( FILES_OUT, "fileexchange_empty.primes" )
        
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out )
        primes_expected = {}
        self.assertTrue( PrimeImplicants.are_equal(primes,primes_expected), str(primes) )

    def test_bnet2primes_missing_inputs(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_missing_inputs.bnet" )
        fname_out = os.path.join( FILES_OUT, "fileexchange_missing_inputs.primes" )
        
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out )
        primes_expected = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(primes,primes_expected), str(primes) )

    def test_bnet2primes_constants(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_constants.bnet" )
        fname_out = os.path.join( FILES_OUT, "fileexchange_constants.primes" )
        
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out )
        primes_expected = {'A': [[{}], []], 'B': [[], [{}]]}
        self.assertTrue( PrimeImplicants.are_equal(primes,primes_expected), str(primes) )

    def test_bnet2primes_stdinout(self):
        fname_in  = os.path.join( FILES_IN,  "fileexchange_constants.bnet" )
        fname_out1 = os.path.join( FILES_OUT, "fileexchange_stdout1.primes" )
        fname_out2 = os.path.join( FILES_OUT, "fileexchange_stdout2.primes" )
        file_in = "A, 0\nB, 1"

        expected = {"A":[[{}],[]],"B":[[],[{}]]}
        
        primes = FileExchange.bnet2primes( BNET=fname_in )
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue( PrimeImplicants.are_equal(primes,expected), msg )
        
        primes = FileExchange.bnet2primes( BNET=file_in )
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue( PrimeImplicants.are_equal(primes,expected), msg )
                                                          
        primes = FileExchange.bnet2primes( BNET=fname_in, FnamePRIMES=fname_out1 )
        msg = "expected: %s\ngot: %s"%(str(expected), str(primes))
        self.assertTrue( PrimeImplicants.are_equal(primes,expected), msg )

    def test_primes2bnet(self):
        fname = os.path.join( FILES_OUT, "fileexchange_primes2bnet.primes" )
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        FileExchange.primes2bnet( Primes=primes, FnameBNET=fname )
        FileExchange.primes2bnet( Primes=primes, FnameBNET=fname, Minimize=True )
        
        # no assertion
        


    def test_read_primes(self):
        fname  = os.path.join( FILES_IN, "fileexchange_missing_inputs.primes" )
        
        primes = FileExchange.read_primes( FnamePRIMES=fname )
        primes_expected = {'B': [[{'B': 0}], [{'B': 1}]], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        self.assertTrue( PrimeImplicants.are_equal(primes,primes_expected), str(primes) )

    def test_read_write_primes(self):
        fname  = os.path.join( FILES_OUT, "fileexchange_read_write.primes" )
        
        primes_write = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        FileExchange.write_primes( Primes=primes_write, FnamePRIMES=fname )
        primes_read = FileExchange.read_primes( FnamePRIMES=fname )

        msg = 'wrote primes \n"{p1}" \nbut got \n"{p2}".'.format(p1=str(primes_write), p2=str(primes_read))
        self.assertTrue( PrimeImplicants.are_equal(primes_read,primes_write), msg )

    def test_primes2genysis(self):
        fname = os.path.join( FILES_OUT, "fileexchange_primes2genysis.genysis" )
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        FileExchange.primes2genysis( Primes=primes, FnameGENYSIS=fname )
        ## no assertion ##

    def test_primes2bns(self):
        fname = os.path.join( FILES_OUT, "fileexchange_primes2bns.bns" )
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        FileExchange.primes2bns( Primes=primes, FnameBNS=fname )
        ## no assertion ##

    def test_primes2smv(self):
        primes = {'vB': [[{}], []], 'vC': [[{'vC': 0}], [{'vC': 1}]], 'vA': [[{'vB': 0, 'vC': 1}], [{'vC': 0}, {'vB': 1}]]}

        fname = os.path.join( FILES_OUT, "fileexchange_primes2smv_syn.smv" )
        ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="synchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        fname = os.path.join( FILES_OUT, "fileexchange_primes2smv_async.smv" )
        ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="asynchronous", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        fname = os.path.join( FILES_OUT, "fileexchange_primes2smv_mixed.smv" )
        ModelChecking.primes2smv(Primes=primes, FnameSMV=fname, Update="mixed", InitialStates="INIT TRUE", Specification="CTLSPEC TRUE")
        ## no assertion ##

    def test_primes2asp(self):
        primes = {'B': [[{}], []], 'C': [[{'C': 0}], [{'C': 1}]], 'A': [[{'B': 0, 'C': 1}], [{'C': 0}, {'B': 1}]]}
        
        for i, (cbounds, cproj) in enumerate(itertools.product([None,(1,2)],[None,['A','B']])):
            fname = os.path.join( FILES_OUT, "fileexchange_primes2asp_case%i.asp"%i )
            TrapSpaces.primes2asp( Primes=primes, FnameASP=fname, Bounds=cbounds, Project=cproj, InsideOf={}, OutsideOf={} )
        ## no assertion ##


class TestInteractionGraphs(unittest.TestCase):

    def test_outdag(self):
        igraph = networkx.DiGraph()
        igraph.add_edges_from([(1,1),(2,1),(2,3),(3,2),(2,4),(4,1),(4,5),(5,6),(6,6),(5,7)])
        outdag = InteractionGraphs.find_outdag(igraph)
        msg = "\nexpected: "+str([7])
        msg+= "\ngot:      "+str(outdag)
        self.assertTrue( outdag == [7], msg )
                              

    def test_activities2animation(self):
        fname_in  = os.path.join( FILES_IN,  "irma.primes" )
        fname_out1 = os.path.join( FILES_OUT, "irma*.png" )
        fname_out2 = os.path.join( FILES_OUT, "irma.gif" )
        primes = FileExchange.read_primes(FnamePRIMES=fname_in)
        igraph = InteractionGraphs.primes2igraph(primes)
        
        activities = [{"gal":0, "Cbf1":1, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":1, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":1, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":0, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":0, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":1, "Swi5":1},
                      {"gal":1, "Cbf1":0, "Gal80":0, "Ash1":1, "Gal4":1, "Swi5":0},
                      ]

        InteractionGraphs.activities2animation(IGraph=igraph, Activities=activities, FnameTMP=fname_out1, FnameGIF=fname_out2)
        # no assertion

    def test_primes2igraph1(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_irma.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        nodes_edges = sorted(igraph.nodes()) + sorted(igraph.edges())
        expected =  ['Ash1', 'Cbf1', 'Gal4', 'Gal80', 'Swi5', 'gal',
                     ('Ash1', 'Cbf1'), ('Cbf1', 'Ash1'), ('Gal4', 'Swi5'), ('Gal80', 'Gal4'),
                     ('Swi5', 'Gal4'), ('gal', 'Ash1'), ('gal', 'Gal80'), ('gal', 'gal')]

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(sorted(igraph.nodes()) + sorted(igraph.edges()))
        self.assertTrue( nodes_edges == expected, msg )

    def test_primes2igraph2(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_irma.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('Ash1', {}), ('Cbf1', {}), ('Gal4', {}), ('Gal80', {}), ('Swi5', {}), ('gal', {}),
                     ('Ash1', 'Cbf1', {'sign': {1}}), ('Cbf1', 'Ash1', {'sign': {1}}), ('Gal4', 'Swi5', {'sign': {-1}}),
                     ('Gal80', 'Gal4', {'sign': {1}}), ('Swi5', 'Gal4', {'sign': {-1}}), ('gal', 'Ash1', {'sign': {1}}),
                     ('gal', 'Gal80', {'sign': {-1}}), ('gal', 'gal', {'sign': {1}})]

        msg = "\nexpected: "+str(expected)
        msg+= "\ngot:      "+str(sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)))
        self.assertTrue( nodes_edges == expected, msg )

    def test_primes2igraph3(self):
        primes = {'A': [[{'A':0}], [{'A':1}]], 'B': [[{}], []], 'C': [[{'B': 0}], [{'B': 1}]]}
                  
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('A', {}), ('B', {}), ('C', {}),
                     ('A', 'A', {'sign': {1}}), ('B', 'C', {'sign': {1}})]
        self.assertTrue( nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)) )

    def test_primes2igraph3(self):
        primes = {'A': [[{}],[]], 'B': [[{'B':0}],[{'B':1}]], 'C': [[{'C':1}],[{'C':0}]], 'D': [[{'B':0,'C':0},{'B':1,'C':1}],
                                                                                                [{'B':1,'C':0},{'B':0,'C':1}]]}
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        nodes_edges = sorted(igraph.nodes(data=True)) + sorted(igraph.edges(data=True))
        expected =  [('A', {}), ('B', {}), ('C', {}), ('D', {}), ('B', 'B', {'sign': {1}}),
                     ('B', 'D', {'sign': {1, -1}}), ('C', 'C', {'sign': {-1}}), ('C', 'D', {'sign': {1, -1}})]
        self.assertTrue( nodes_edges == expected, sorted(igraph.nodes(data=True))+sorted(igraph.edges(data=True)) )

    def test_igraph2dot(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_irma.primes" )
        fname_out = os.path.join( FILES_OUT, "interactiongraphs_igraph2dot.dot" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out )
        ## no assertion ##

    def test_igraph2dot_string(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_irma.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=None )
        ## no assertion ##

    def test_igraph2image(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_irma.primes" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        fname_out = os.path.join( FILES_OUT, "interactiongraphs_igraph2image.jpg" )
        InteractionGraphs.igraph2image( IGraph=igraph, FnameIMAGE=fname_out )
        ## no assertion ##

    def test_dot2image(self):
        fname_in = os.path.join( FILES_IN, "interactiongraphs_topology.dot" )
        fname_out1 = os.path.join( FILES_OUT, "interactiongraphs_dot2image1.jpg" )
        fname_out2 = os.path.join( FILES_OUT, "interactiongraphs_dot2image2.svg" )
        fname_out3 = os.path.join( FILES_OUT, "interactiongraphs_dot2image3.eps" )
        fname_out4 = os.path.join( FILES_OUT, "interactiongraphs_dot2image4.gif" )
        
        InteractionGraphs.dot2image( FnameDOT=fname_in, FnameIMAGE=fname_out1 )
        InteractionGraphs.dot2image( FnameDOT=fname_in, FnameIMAGE=fname_out2 )
        InteractionGraphs.dot2image( FnameDOT=fname_in, FnameIMAGE=fname_out3 )
        InteractionGraphs.dot2image( FnameDOT=fname_in, FnameIMAGE=fname_out4 )
        ## no assertion ##    

    def test_styles(self):
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
        fname_out_dot = os.path.join( FILES_OUT, "interactiongraphs_style_interactionsigns.dot" )
        fname_out_pdf = os.path.join( FILES_OUT, "interactiongraphs_style_interactionsigns.pdf" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        InteractionGraphs.add_style_interactionsigns( IGraph=igraph )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )
        InteractionGraphs.dot2image( FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf )
        InteractionGraphs.igraph2image( IGraph=igraph, FnameIMAGE=fname_out_pdf )

        fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
        fname_out_dot = os.path.join( FILES_OUT, "interactiongraphs_style_activities.dot" )
        fname_out_pdf = os.path.join( FILES_OUT, "interactiongraphs_style_activities.pdf" )

        InteractionGraphs.add_style_interactionsigns( IGraph=igraph )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )
        InteractionGraphs.dot2image( FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf )
        InteractionGraphs.igraph2image( IGraph=igraph, FnameIMAGE=fname_out_pdf )

        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        activities = {'v1':1,'v2':0,'v3':1,'v4':1,'v5':1,'v6':0}
        InteractionGraphs.add_style_activities( IGraph=igraph, Activities=activities )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )
        InteractionGraphs.dot2image( FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf )
        
        fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
        fname_out_dot = os.path.join( FILES_OUT, "interactiongraphs_style_sccs.dot" )
        fname_out_pdf = os.path.join( FILES_OUT, "interactiongraphs_style_sccs.pdf" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        InteractionGraphs.add_style_sccs( IGraph=igraph )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )
        InteractionGraphs.dot2image( FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf )

        fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
        fname_out_pdf = os.path.join( FILES_OUT, "interactiongraphs_style_ioc.pdf" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        InteractionGraphs.add_style_inputs( IGraph=igraph )
        InteractionGraphs.add_style_constants( IGraph=igraph )
        InteractionGraphs.add_style_outputs( IGraph=igraph )
        InteractionGraphs.igraph2image( IGraph=igraph, FnameIMAGE=fname_out_pdf )

        fname_in  = os.path.join( FILES_IN, "interactiongraphs_topology.primes" )
        fname_out_pdf = os.path.join( FILES_OUT, "interactiongraphs_style_subgrapghs.pdf" )
        fname_out_dot = os.path.join( FILES_OUT, "interactiongraphs_style_subgrapghs.dot" )
        primes = FileExchange.read_primes( FnamePRIMES=fname_in )
        
        igraph = InteractionGraphs.primes2igraph( Primes=primes )
        subgraphs = [["v1","v2"],(["v3","v4"],{"label":"jo"})]
        InteractionGraphs.add_style_subgraphs( IGraph=igraph, Subgraphs=subgraphs )
        InteractionGraphs.igraph2dot( IGraph=igraph, FnameDOT=fname_out_dot )
        InteractionGraphs.dot2image( FnameDOT=fname_out_dot, FnameIMAGE=fname_out_pdf )

        ## no assertion ##

    



if __name__=="__main__":


    
    if 0:
        # run all tests
        update_input_files()
        unittest.main(verbosity=2, buffer=True)

    if 1:
        # run single test
        suite = unittest.TestSuite()
        suite.addTest(TestStateTransitionGraphs("test_stg2sccgraph"))
        suite.addTest(TestStateTransitionGraphs("test_stg2condensationgraph"))
        suite.addTest(TestStateTransitionGraphs("test_stg2htg"))
        
        runner = unittest.TextTestRunner()
        runner.run(suite)

    if 0:
        # run test class

        import inspect

        class_name = TestModelChecking

        suite = unittest.TestSuite()
        for name, obj in inspect.getmembers(class_name):
            if name.startswith("test_"):
                suite.addTest(class_name(name))

        runner = unittest.TextTestRunner()
        runner.run(suite)
            
            
        
            
    







