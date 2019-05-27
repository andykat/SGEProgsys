import random
import copy
import math
from enum import Enum
import networkx as nx
from collections import defaultdict
from multiprocessing import Pool
import os
import json
import signal

class TimeoutException(Exception):   # Custom exception class
    pass

def timeout_handler(signum, frame):   # Custom signal handler
    # raise TimeoutException
    # print("timeout exception")
    pass

class SGE:

    def __init__(self, file_name):
        self.file_name = file_name
        self.rules = {}
        self.non_terminals = []
        random.seed()
        self.population_size = 100
        self.genotype_max = 99999999  # maximum value for each integer
        self.genotype_min = 0  # minimum value for each integer

        self.tournament_k = 7  # number of entrants for each tournament
        self.tournament_p = 0.7  # probability of selecting winner
        self.top_performing_carry = 3  # number of top performing sequences from previous population carried over

        self.gene_mutation_chance = 0.15  # chance that a gene mutates
        self.average_best_fitness = []
        self.average_best_fitness_N = 5 # calculation of average top fitness to print out

        self.recursion_max = 2  # level of recursion

        self.helper_code = ""
        self.test_string = ""
        self.train_string = ""
        
        self.final_nonterminal = ""

        self.references_count = {}
        self.gene_expansion_count = {}

        self.currentPopulation = []
        self.fitness = []
        self.fitness_indicies = []
        self.highest_performers = []
        self.highest_fitnesses = []
        self.population_nonterminal_count = []
        self.newpopulation = []

        self.fitness_cache = {}
        self.cache_use_per_iteration = []
        self.iteration_cache_use_count = 0

        self.grammar_replacement = {"greater_equal_than": ">=",
                                    "less_equal_than": "<=", "loop_break_constant": "10",
                                    "greater_than": ">", "less_than": "<"}

        self.graph = nx.Graph()
        self.nonterminals_in_cycle = []

        self.is_referenced_by = {}
        self.possible_rhs_for_endcycle = {}
        self.not_possible_rhs_for_endcycle = {}
        self.nonterminal_terminates = set()
        self.secondary_nonterminal_terminates = set()
        self.count_iteration = 0
        signal.signal(signal.SIGALRM, timeout_handler)

    def read_supplementary_files(self):
        """
        reads helper code, and testing and training datasets
        :return:
        """
        f_name = "../helper_codes/" + self.file_name + "_Helper.txt"
        with open(f_name) as fp:
            self.helper_code = fp.read()

        f_name = "../datasets/" + self.file_name + "_Test.txt"
        with open(f_name) as fp:
            self.test_string = fp.read()

        f_name = "../datasets/" + self.file_name + "_Train.txt"
        with open(f_name) as fp:
            self.train_string = fp.read()

        self.helper_code = self.helper_code.replace("<train>", self.train_string.replace("\n", "\n  "))

    def read_bnf_file(self):
        """
        Reads the grammar file and converts it into a grammar
        Runs methods to calculate cycles and create a grammar that minimizes cycles
        :return:
        """
        equation_split = " ::= "
        f_name = "../grammars/" + self.file_name + ".bnf"
        count = 0
        for line in open(f_name, 'r'):
            # take left hand
            if line.startswith("<") and equation_split in line:
                t_split = line.split(equation_split)
                lhs = t_split[0].strip()
                # print(lhs)
                rhs = t_split[1].strip("\n")

                # transform rhs into orGroup of expressions
                or_separated_list = rhs.split("|")

                o = OrGroup()

                for production in or_separated_list:
                    expression = production.split("'")
                    s = Sentence()
                    for obj in expression:
                        if obj != "":
                            if "<" in obj:
                                obj_copy = obj[:]
                                while "<" in obj_copy:
                                    start_index = obj_copy.find("<")
                                    end_index = obj_copy.find(">")
                                    sub_string = obj_copy[start_index: end_index+1]
                                    obj_copy = obj_copy[end_index+1:]
                                    s.append_object(sub_string, TerminalType.NONTERMINAL)

                            else:
                                obj = obj.replace("\\n", "\n")
                                for replace_key in self.grammar_replacement:
                                    obj = obj.replace(replace_key, self.grammar_replacement[replace_key])

                                s.append_object(obj, TerminalType.TERMINAL)
                    o.expressions.append(s)

                self.rules[lhs] = Production(lhs, o)
                if count == 0:
                    self.final_nonterminal = lhs
                    count += 1

        # self.process_grammar_recursion()
        # print("processing grammar cycles")
        self.process_grammar_cycles()
        # for rule_lhs, rule in self.rules.items():
        #     print("lhs:" + rule_lhs)
        #
        #     for expression in rule.rhs.expressions:
        #         for ob in expression.objects:
        #             print(ob, end='')
        #         print("|", end='')
        #     print("\n")

        # for lhs, rule in self.rules.items():
        #     self.non_terminals.append(lhs)
        # print("\nnonterminals")
        # print(self.non_terminals)
        # print("\n")

        # Calculating expansions is not needed because we append genotypes when we need
        # more to result in a correct phenotype

        # self.calculate_expansions_dfs_start()
        # print("\ndfs expansion count:")
        # print(self.gene_expansion_count)

    def process_grammar_cycles(self):
        """
        Gets the cycle data that we have calculated and converts the grammar to minimize cycles
        :return:
        """
        self.find_grammar_cycle_end_points()
        self.create_grammar_graph()
        lhs_queue = [self.final_nonterminal]
        has_popped = []
        # print("terminated")
        # print(self.nonterminal_terminates)
        while len(lhs_queue) > 0:
            lhs = lhs_queue.pop(0)
            self.non_terminals.append(lhs[:])
            has_popped.append(lhs)
            or_group = self.rules[lhs].rhs
            for expression in or_group.expressions:
                for i in range(0, len(expression.objects)):
                    if expression.object_types[i] == TerminalType.NONTERMINAL:
                        t_nt = expression.objects[i]
                        if (t_nt not in has_popped) and (t_nt not in lhs_queue) and 'lvl' not in t_nt:
                            lhs_queue.append(t_nt)

            if lhs in self.nonterminals_in_cycle:
                # create levels of the nonterminal
                for i in range(0, self.recursion_max):
                    will_add_rule_flag = True
                    or_group_deep_copy = copy.deepcopy(or_group)
                    new_or_group = copy.deepcopy(or_group)
                    new_lhs = copy.deepcopy(lhs)
                    # append lvl-1 to the lfh expression
                    if i > 0:
                        new_lhs = self.append_level_to_nonterminal(lhs, i - 1)
                    # new_nt = self.append_level_to_nonterminal(lhs, i)

                    if i < self.recursion_max - 1:
                        for j in range(0, len(or_group_deep_copy.expressions)):
                            expression = or_group_deep_copy.expressions[j]
                            for k in range(0, len(expression.objects)):
                                # if expression.objects[k] == lhs and expression.object_types[k] == TerminalType.NONTERMINAL:
                                if expression.object_types[k] == TerminalType.NONTERMINAL:
                                    # check is object is in a cycle
                                    if expression.objects[k] in self.nonterminals_in_cycle:
                                        nonterminal_lvl_string = self.append_level_to_nonterminal(expression.objects[k], i)
                                        # if i == 0:
                                        #     nonterminal_lvl_string = copy.deepcopy(expression.objects[k])
                                        # new_or_group.expressions[j].objects[k] = new_nt
                                        new_or_group.expressions[j].objects[k] = nonterminal_lvl_string

                    else:
                        # May change later:
                        # For the last level, we remove any expressions that include nonterminals part of a cycle
                        # if the or group is empty, then we do not add it
                        new_or_group = OrGroup()
                        for j in range(len(or_group_deep_copy.expressions)):
                            # check if this rhs can lead to a non cycle
                            leads_to_non_cycle = False
                            if j in self.possible_rhs_for_endcycle[lhs]:
                                leads_to_non_cycle = True
                            else:
                                leads_to_non_cycle = True
                                # check if one of the expressions has an expression that terminates
                                expression = or_group_deep_copy.expressions[j]
                                for k in range(0, len(expression.objects)):
                                    if expression.object_types[k] == TerminalType.NONTERMINAL:
                                        if expression.objects[k] not in self.nonterminal_terminates \
                                                or lhs == expression.objects[k]:
                                            leads_to_non_cycle = False
                                            break

                            if leads_to_non_cycle:
                                expression = copy.deepcopy(or_group_deep_copy.expressions[j])
                                for k in range(0, len(expression.objects)):
                                    if expression.object_types[k] == TerminalType.NONTERMINAL:
                                        # check is object is in a cycle
                                        if expression.objects[k] in self.nonterminals_in_cycle:
                                            nonterminal_lvl_string = self.append_level_to_nonterminal(
                                                expression.objects[k], i-1)  # maintain maximum recursion level
                                            expression.objects[k] = nonterminal_lvl_string

                                # add expression to or group
                                new_or_group.expressions.append(expression)

                    # if or group has no expressions, then nonterminal is never called
                    if len(new_or_group.expressions) == 0:
                        # print("blank!!")
                        # print(new_lhs)
                        # print(self.possible_rhs_for_endcycle[lhs])
                        new_or_group.expressions.append(copy.deepcopy(self.rules['<blank>'].rhs.expressions[0]))

                    self.rules[new_lhs] = Production(new_lhs, new_or_group)
                    if new_lhs not in self.non_terminals:
                        self.non_terminals.append(new_lhs)

    def create_grammar_graph(self):
        """
        Calculates cycles
        :return:
        """
        for rule_lhs, rule in self.rules.items():
            for expression in rule.rhs.expressions:
                for i in range(len(expression.objects)):
                    if expression.object_types[i] == TerminalType.NONTERMINAL:
                        self.graph.add_edge(rule_lhs, expression.objects[i])

        # print(nx.cycle_basis(self.graph, self.final_nonterminal))
        cycle_basis = nx.cycle_basis(self.graph, self.final_nonterminal)
        for cycle in cycle_basis:
            for node in cycle:
                if node not in self.nonterminals_in_cycle:
                    self.nonterminals_in_cycle.append(node)

    def find_grammar_cycle_end_points(self):
        """
        Finds the paths through the grammar which will terminate so that the last level
        of recursion can end correctly
        :return:
        """
        intial_set = {self.final_nonterminal}
        # intial_set = [self.final_nonterminal]
        for rule_lhs, _ in self.rules.items():
            self.possible_rhs_for_endcycle[rule_lhs] = []
            self.not_possible_rhs_for_endcycle[rule_lhs] = []

        self.grammar_dps(self.final_nonterminal, intial_set)

        for lhs in self.possible_rhs_for_endcycle:
            if len(self.possible_rhs_for_endcycle[lhs]) > 0:
                self.nonterminal_terminates.add(lhs)

        # print("non cycle endings")
        # print(self.possible_rhs_for_endcycle)

    def grammar_dps(self, current_nt, nt_set):
        """
        dfs through the grammar to find noncyclical paths
        :param current_nt:
        :param nt_set:
        :return:
        """
        nt_terminates = False
        # if current_nt == "<int>":
        #     print("nt_set")
        #     print(nt_set)
        for i in range(len(self.rules[current_nt].rhs.expressions)):
            expression = self.rules[current_nt].rhs.expressions[i]
            expression_terminates = True
            for j in range(len(expression.objects)):
                if expression.object_types[j] == TerminalType.NONTERMINAL:
                    # if expression.objects[j] in self.possible_rhs_for_endcycle[curren]
                    if expression.objects[j] not in nt_set:
                        nt_set.add(expression.objects[j])
                        # nt_set.append(expression.objects[j])
                        did_complete = self.grammar_dps(expression.objects[j], nt_set)
                        if not did_complete:
                            # if current_nt == "<int_var>":
                            # print("didn't terminate becuaes of:")
                            # print(nt_set)
                            # print(expression.objects[j])
                            expression_terminates = False
                        nt_set.remove(expression.objects[j])
                    else:
                        expression_terminates = False

            if expression_terminates:
                if i not in self.possible_rhs_for_endcycle[current_nt]:
                    if i not in self.not_possible_rhs_for_endcycle[current_nt]:
                        self.possible_rhs_for_endcycle[current_nt].append(i)
                nt_terminates = True
            else:
                if i not in self.not_possible_rhs_for_endcycle[current_nt]:
                    self.not_possible_rhs_for_endcycle[current_nt].append(i)
                    # remove impossible rhs from possible rhs
                    if i in self.possible_rhs_for_endcycle[current_nt]:
                        self.possible_rhs_for_endcycle[current_nt].remove(i)

        return nt_terminates

    # Calculating expansions is not needed because we append genotypes when we need
    # more to result in a correct phenotype

    # def calculate_expansions_dfs_start(self):
    #     self.gene_expansion_count = {self.final_nonterminal: 1}
    #     self.calculate_expansions_dfs(self.final_nonterminal, 1, set())
    #
    #     # remove nonterminals without expansions from nonterminal list
    #     i = 0
    #     while i < len(self.non_terminals):
    #         nt = self.non_terminals[i]
    #         if nt not in self.gene_expansion_count:
    #             self.non_terminals.remove(nt)
    #             i -= 1
    #         i += 1


    # def calculate_expansions_dfs(self, nt, nt_count, current_nonterminals):
    #     if nt in current_nonterminals:
    #         print("cycle?:")
    #         print(nt)
    #     current_nonterminals.add(nt)
    #     expression_count_max = {}
    #     for i in range(len(self.rules[nt].rhs.expressions)):
    #         expression = self.rules[nt].rhs.expressions[i]
    #         expression_count = {}
    #         for j in range(len(expression.objects)):
    #             if expression.object_types[j] == TerminalType.NONTERMINAL:
    #                 t_nt = expression.objects[j]
    #                 if t_nt in expression_count:
    #                     expression_count[t_nt] += 1
    #                 else:
    #                     expression_count[t_nt] = 1
    #         for t_nt in expression_count:
    #             if t_nt in expression_count_max:
    #                 if expression_count[t_nt] > expression_count_max[t_nt]:
    #                     expression_count_max[t_nt] = expression_count[t_nt]
    #             else:
    #                 expression_count_max[t_nt] = expression_count[t_nt]
    #
    #     for t_nt in expression_count_max:
    #         if t_nt in self.gene_expansion_count:
    #             self.gene_expansion_count[t_nt] += nt_count * expression_count_max[t_nt]
    #         else:
    #             self.gene_expansion_count[t_nt] = nt_count * expression_count_max[t_nt]
    #     for t_nt in expression_count_max:
    #         self.calculate_expansions_dfs(t_nt, expression_count_max[t_nt], current_nonterminals)
    #
    #     current_nonterminals.remove(nt)

    def process_grammar_recursion(self):
        """
        remove recursion in grammar
        :return:
        """
        lhs_queue = [self.final_nonterminal]
        has_popped = []
        while len(lhs_queue) > 0:
            lhs = lhs_queue.pop(0)
            self.non_terminals.append(lhs[:])
            has_popped.append(lhs)
            or_group = self.rules[lhs].rhs
            flag = False
            for expression in or_group.expressions:
                for i in range(0, len(expression.objects)):
                    if expression.objects[i] == lhs and expression.object_types[i] == TerminalType.NONTERMINAL:
                        flag = True
                    if expression.object_types[i] == TerminalType.NONTERMINAL:
                        t_nt = expression.objects[i]
                        if (t_nt not in has_popped) and (t_nt not in lhs_queue):
                            lhs_queue.append(t_nt)

            if flag:
                # recursion found
                for i in range(0, self.recursion_max):
                    or_group_deep_copy = copy.deepcopy(or_group)
                    new_or_group = copy.deepcopy(or_group)
                    new_lhs = copy.deepcopy(lhs)
                    # append lvl-1 to the lfh expression
                    if i > 0:
                        new_lhs = self.append_level_to_nonterminal(lhs, i-1)
                    new_nt = self.append_level_to_nonterminal(lhs, i)

                    if i < self.recursion_max - 1:
                        for j in range(0, len(or_group_deep_copy.expressions)):
                            expression = or_group_deep_copy.expressions[j]
                            for k in range(0, len(expression.objects)):
                                if expression.objects[k] == lhs and expression.object_types[k] == TerminalType.NONTERMINAL:
                                    new_or_group.expressions[j].objects[k] = new_nt

                    else:
                        # for the last level, we must replace the recursive nonterminal with all
                        # possible nonrecursive results
                        new_nt_exp = []
                        has_nt_indices = []
                        has_nt_indices_reverse = []
                        for j in range(0, len(or_group_deep_copy.expressions)):
                            expression = or_group_deep_copy.expressions[j]
                            has_nt = False
                            for k in range(0, len(expression.objects)):
                                if expression.objects[k] == lhs and expression.object_types[k] == TerminalType.NONTERMINAL:
                                    has_nt = True

                            # does not contain the nonterminal, so we save the result
                            if not has_nt:
                                new_nt_exp.append(copy.deepcopy(expression))
                            else:
                                has_nt_indices.append(j)
                                has_nt_indices_reverse.insert(0, j)
                            for j2 in range(0, len(or_group_deep_copy.expressions)):
                                expression = or_group_deep_copy.expressions[j2]
                                for k in range(0, len(expression.objects)):
                                    if expression.objects[k] == lhs and expression.object_types[k] == TerminalType.NONTERMINAL:
                                        new_or_group.expressions[j2].objects[k] = new_nt

                        # remove existing expressions in our new_or_group because we will adding new ones
                        for j in range(0, len(has_nt_indices_reverse)):
                            new_or_group.expressions.pop(has_nt_indices_reverse[j])

                        # add new expressions
                        for j in range(0, len(has_nt_indices)):
                            for k in range(0, len(new_nt_exp)):
                                new_expression = copy.deepcopy(or_group_deep_copy.expressions[has_nt_indices[j]])
                                replace_exp = copy.deepcopy(new_nt_exp[k])
                                new_exp_index = 0
                                while new_exp_index < len(new_expression.objects):
                                    if new_expression.objects[new_exp_index] == lhs and new_expression.object_types[new_exp_index] == TerminalType.NONTERMINAL:
                                        new_expression.objects.pop(new_exp_index)
                                        new_expression.object_types.pop(new_exp_index)
                                        for l in range(0, len(replace_exp.objects)):
                                            new_expression.objects.insert(new_exp_index + l, replace_exp.objects[l])
                                            new_expression.object_types.insert(new_exp_index + l, replace_exp.object_types[l])
                                    else:
                                        new_exp_index += 1
                                new_or_group.expressions.append(new_expression)

                    self.rules[new_lhs] = Production(new_lhs, new_or_group)
                    if new_lhs not in self.non_terminals:
                        self.non_terminals.append(new_lhs)

    @staticmethod
    def append_level_to_nonterminal(stri, level):
        """
        adds the 'level_n' to nonterminals to denote the level of recursion
        :param stri:
        :param level:
        :return:
        """
        position = stri.find('>')
        newstr = ""
        if position < 0:
            print("error: > not found in nonterminal")
        else:
            newstr = stri[:position] + "lvl" + str(level) + stri[position:]

        return newstr

    def initialize_population(self):
        self.currentPopulation = []
        self.fitness = []
        for i in range(0, self.population_size):
            gene_dict = {}
            # for key in self.gene_expansion_count:
            for key in self.non_terminals:
                # genotype_max_length = self.gene_expansion_count[key]
                genotype_max_length = 1
                gene_dict[key] = []
                for j in range(0, genotype_max_length):
                    gene_dict[key].append(self.random_genotype())
            self.currentPopulation.append(gene_dict)
            self.fitness.append(0)

    def random_genotype(self):
        return random.randint(self.genotype_min, self.genotype_max)

    def mutate_child(self, child):
        for nt in self.non_terminals:
            chance = random.uniform(0, 1)
            if chance < self.gene_mutation_chance:
                if len(child[nt]) > 0:
                    rand_index = random.randint(0, len(child[nt]) - 1)
                    child[nt][rand_index] = self.random_genotype()

        return child

    def mutate_parent(self, parent, nonterminal_count):
        for nt in self.non_terminals:
            if random.uniform(0, 1) < self.gene_mutation_chance:
                if nonterminal_count[nt] > 0:
                    rand_index = random.randint(0, nonterminal_count[nt]-1)
                    parent[nt][rand_index] = self.random_genotype()
        return parent

    def recombination_cross(self, parents, nonterminal_counts):
        child = [{}, {}]
        mutated_parents = []
        for parent in parents:
            mutated_parents.append(copy.deepcopy(parent))
        # mutate genes
        for i in range(0, len(mutated_parents)):
            mutated_parents[i] = self.mutate_parent(mutated_parents[i], nonterminal_counts[i])

        for nt in self.non_terminals:
            rand_n = random.randint(0, 1)
            # max = nonterminal_counts[randN][nt]
            t_max = min(nonterminal_counts[0][nt], nonterminal_counts[1][nt])
            # crossoverPoint = random.randint(0, len(parents[randN][nt]) - 1)
            # if max == 0:
            #     max = random.randint(0, len(parents[randN][nt]) - 1)
            crossover_point = random.randint(0, t_max)
            other_n = rand_n + 1
            if other_n == 2:
                other_n = 0
            child[0][nt] = []
            child[1][nt] = []

            child[0][nt] = child[0][nt] + mutated_parents[rand_n][nt][:crossover_point]
            child[0][nt] = child[0][nt] + mutated_parents[other_n][nt][crossover_point:]
            child[1][nt] = child[1][nt] + mutated_parents[other_n][nt][:crossover_point]
            child[1][nt] = child[1][nt] + mutated_parents[rand_n][nt][crossover_point:]

        return child
    
    def mutation(self, seq):
        for nt in self.non_terminals:
            chance = random.uniform(0, 1)
            if chance < self.gene_mutation_chance:
                rand_index = random.randint(0, len(seq[nt])-1)
                seq[nt][rand_index] = self.random_genotype()
        return seq

    def translate_seq_to_phenotype(self, genes, remove_nonterminals=True):
        """
        Converts genotype into a phenotype
        :param genes:
        :param remove_nonterminals:
        :return:
        """
        cur_objects = []
        curobject_types = []
        cur_objects.append(self.final_nonterminal)
        curobject_types.append(TerminalType.NONTERMINAL)
        nonterminal_count = {}
        nonterminal_index_start = 0
        loop_break_count = 0
        # print("genes")
        # print(genes)
        for nt in self.non_terminals:
            nonterminal_count[nt] = 0
        while TerminalType.NONTERMINAL in curobject_types:
            # find next non terminal
            non_terminal_object = ""
            nonterminal_index = -1
            for i in range(nonterminal_index_start, len(curobject_types)):
                if curobject_types[i] == TerminalType.NONTERMINAL:
                    non_terminal_object = cur_objects[i]

                    nonterminal_index = i
                    break
                else:
                    nonterminal_index_start = i
            if nonterminal_index < 0:
                print("no terminalfound")
                break
            # print(non_terminal_object)
            rule = self.rules[non_terminal_object]
            or_group = rule.rhs
            n_or_groups = len(or_group.expressions)

            # select an expression from or groups
            if nonterminal_count[non_terminal_object] >= len(genes[non_terminal_object]):
                # !! create new value
                genes[non_terminal_object].append(self.random_genotype())

            value = genes[non_terminal_object][nonterminal_count[non_terminal_object]]
            nonterminal_count[non_terminal_object] += 1
            index = value % n_or_groups
            expression = or_group.expressions[index]
            # replace loopbreak in expression
            # if non_terminal_object == "<blank>":
            #     print("found blank")
            # replace non terminal with new expression
            cur_objects.pop(nonterminal_index)
            curobject_types.pop(nonterminal_index)
            found_loop_break = False
            for i in range(0, len(expression.objects)):
                exp = expression.objects[i]
                if "loopBreak" in expression.objects[i]:
                    exp = exp.replace("loopBreak%", "loopBreak" + str(loop_break_count))
                    found_loop_break = True

                cur_objects.insert(nonterminal_index + i, exp)
                curobject_types.insert(nonterminal_index + i, expression.object_types[i])
            if found_loop_break:
                loop_break_count += 1
        # print("cur_objects")
        # print(cur_objects)
        if remove_nonterminals:
            i = 0
            while i < len(cur_objects):
                if curobject_types[i] == TerminalType.NONTERMINAL:
                    cur_objects.pop(i)
                    curobject_types.pop(i)
                    i -= 1
                i += 1
            # print(cur_objects)
            return [[cur_objects, curobject_types], nonterminal_count]

        return [[cur_objects, curobject_types], nonterminal_count]

    # returns a tournament selected genotype
    def tournament_selection(self, k):
        selected = []
        for i in range(0, k):
            selected.append(random.randint(0, self.population_size-1))
        selected = sorted(selected)

        for i in range(0, k):
            x = random.uniform(0, 1)
            if x < self.tournament_p:
                # return self.currentPopulation[self.fitness_indicies[selected[i]][0]]
                return self.fitness_indicies[selected[i]][0]
        # return self.currentPopulation[self.fitness_indicies[selected[0]][0]]
        return self.fitness_indicies[selected[0]][0]

    def create_children(self):
        parents = []
        parent0index = self.tournament_selection(self.tournament_k)
        parent1index = self.tournament_selection(self.tournament_k)
        parents.append(self.currentPopulation[parent0index])
        parents.append(self.currentPopulation[parent1index])
        nonterminal_counts = [self.population_nonterminal_count[parent0index], self.population_nonterminal_count[parent1index]]

        children = self.recombination_cross(parents, nonterminal_counts)
        return children

    def run_iterations(self, iterations):
        """
        Main function
        Creates the population, and runs step() for each generation
        :param iterations:
        :return:
        """
        self.initialize_population()
        self.average_best_fitness = []
        self.cache_use_per_iteration = []

        # run the iterations
        iteration_count = 0
        success_flag = False
        for i in range(0, iterations):
            self.count_iteration = i
            if i % 25 == 0:
                print("iteration: " + str(i))
            iteration_count += 1
            success_flag = self.step()
            if success_flag:
                break

        # get highest performers
        for i in range(0, self.population_size):
            seq = self.currentPopulation[i]
            phen = self.translate_seq_to_phenotype(seq)[0][0]
            code = self.translate_objects_into_code(phen)
            self.fitness[i] = self.calculate_fitness(code, increase_cache_count=False)
            # get the top performing sequences

        self.fitness_indicies = []
        for i in range(0, self.population_size):
            self.fitness_indicies.append([i, self.fitness[i]])

        sorted(self.fitness_indicies, key=lambda x: x[1], reverse=True)
        self.highest_performers = []
        self.highest_fitnesses = []
        number_of_top_performers = 5

        for i in range(0, number_of_top_performers):
            phen = self.translate_seq_to_phenotype(self.currentPopulation[self.fitness_indicies[i][0]])[0][0]
            code = self.translate_objects_into_code(phen)
            tabbed_code = self.insert_tabs(code)
            # self.highest_performers.append(self.currentPopulation[self.fitness_indicies[i][0]])
            self.highest_performers.append(tabbed_code)
            self.highest_fitnesses.append(self.fitness_indicies[i][1])
        # print(self.highest_fitnesses[0])
        return [self.highest_performers, self.highest_fitnesses, success_flag, iteration_count,
                self.cache_use_per_iteration]

    # def fitness_subprocess(phen):
    #     code = self.translate_objects_into_code(phen)
    #     return self.calculate_fitness(code)

    def step(self):
        """
        Goes through one generation
        :return:
        """
        self.population_nonterminal_count = []
        self.iteration_cache_use_count = 0
        # print("getting fitness")
        # get the fitness of all sequences
        for i in range(0, self.population_size):
            # print(i)
            seq = self.currentPopulation[i]
            # print("translate seq to phen")
            result = self.translate_seq_to_phenotype(seq, remove_nonterminals=True)
            phen = result[0][0]
            nonterminal_count = result[1]
            self.population_nonterminal_count.append(nonterminal_count)
            # print("translate to code")
            code = self.translate_objects_into_code(phen)
            # self.fitness[i] = self.harmonicFitness(phen)
            # print("calculate fitness")
            self.fitness[i] = self.calculate_fitness(code)

        # get the top performing sequences

        self.fitness_indicies = []
        for i in range(0, self.population_size):
            self.fitness_indicies.append([i, self.fitness[i]])

        self.fitness_indicies = sorted(self.fitness_indicies, key=lambda x: x[1], reverse=True)

        afitness = 0.0
        for i in range(0, self.average_best_fitness_N):
            afitness += self.fitness_indicies[i][1]
        afitness /= -float(self.average_best_fitness_N)
        self.average_best_fitness.append(afitness)

        self.newpopulation = []

        # add the best performing sequence from last population
        for i in range(0, self.top_performing_carry):
            self.newpopulation.append(copy.deepcopy(self.currentPopulation[self.fitness_indicies[i][0]]))

        # fill in the rest of the new population with children
        while len(self.newpopulation) < self.population_size:
            # crossed children
            children = self.create_children()

            self.newpopulation.append(children[0])
            if len(self.newpopulation) < self.population_size:
                self.newpopulation.append(children[1])

        # print top performers
        # print("Top Performers:")
        #
        if self.count_iteration % 25 == 0:
            print("Top Average Fitness: %.2f" % afitness)
        #
        # for i in range(0, 1):
        #     phen = self.translate_seq_to_phenotype(self.currentPopulation[self.fitness_indicies[i][0]])[0][0]
        #     stri = ""
        #     # for o in phen:
        #     #     stri = stri + o
        #     print(stri + ":" + str(self.fitness_indicies[i][1]) + "   seqlength:" + str(len(self.currentPopulation[self.fitness_indicies[i][0]])) )
        # print("\n")
        flag = False
        if math.fabs(self.fitness_indicies[0][1]) < 0.0001:
            flag = True

        self.currentPopulation = self.newpopulation
        self.cache_use_per_iteration.append(self.iteration_cache_use_count)
        return flag

    def translate_objects_into_code(self, objects):
        """
        Formats the phenotype correctly into code
        :param objects:
        :return:
        """
        # print("translate_objects_into_code")
        # print(objects)
        code = ""
        for s in objects:
            code += s

        # return self.python_filter(code)
        return self.insert_tabs(code)

    def calculate_fitness(self, code, increase_cache_count=True):
        if code in self.fitness_cache:
            if increase_cache_count:
                self.iteration_cache_use_count += 1
            return self.fitness_cache[code]
        # print("code")
        # print("------------------------------------------------------")
        # print(code)
        # print("------------------------------------------------------")

        final_code = self.helper_code.replace("<insertCodeHere>", code)

        error = 0.0
        signal.alarm(1.0)
        # signal.setitimer(signal.ITIMER_REAL, 0.1)
        try:
            loc = {}
            exec(final_code, loc, loc)
            error = loc['quality']
        except TimeoutException:
            # print("Timeout exception")
            error = 9999999
        except Exception as e:
            # print("Error in code")
            # print(e)
            # print("code")
            # print("------------------------------------------------------")
            # print(code)
            # print("------------------------------------------------------")
            # print("finalcode")
            # print("------------------------------------------------------")
            # print(final_code)
            # print("------------------------------------------------------")
            error = 9999999

        # try:
        signal.alarm(0)
        # except Exception as e:
        #     signal.signal(signal.SIGALRM, timeout_handler)

        self.fitness_cache[code] = -error

        return -error

    @staticmethod
    def calc_min(a, b):
        if a < b:
            return a
        return b

    @staticmethod
    def insert_tabs(code):
        flag = False
        indentation = 0
        newcode = ""
        while not flag:
            new_line_index = code.find("\n")
            if new_line_index < 0:
                # flag = True
                break
            else:
                # print(code[new_line_index+2])
                if code[new_line_index - 2:new_line_index] == '{:':
                    indentation += 1
                    code = code[:new_line_index - 2] + code[new_line_index:]
                    new_line_index -= 2
                elif code[new_line_index + 1:new_line_index + 3] == ':}':
                    indentation -= 1
                    code = code[:new_line_index + 1] + code[new_line_index + 3:]
                    # new_line_index -= 2
                tabs = ""
                for i in range(0, indentation+1):
                    tabs += "  "
                newcode += code[:new_line_index] + "\n" + tabs
                code = code[new_line_index + 1:]
        newcode += code
        return newcode

    @staticmethod
    def python_filter(txt):
        """ Create correct python syntax.
        We use {: and :} as special open and close brackets, because
        it's not possible to specify indentation correctly in a BNF
        grammar without this type of scheme."""
        print("nonindented code")
        print(txt)
        indent_level = 0
        tmp = txt[:]
        i = 0
        while i < len(tmp):
            tok = tmp[i:i + 2]
            if tok == "{:":
                indent_level += 1
            elif tok == ":}":
                indent_level -= 1
            tabstr = "\n" + "  " * indent_level
            if tok == "{:" or tok == ":}":
                tmp = tmp.replace(tok, tabstr, 1)
            i += 1
        # Strip superfluous blank lines.
        txt = "\n".join([line for line in tmp.split("\n")
                         if line.strip() != ""])
        return txt


class TerminalType(Enum):
    TERMINAL = 0
    NONTERMINAL = 1


class Production:
    # lhs is a nonterminal
    # rhs is an OrGroup of Sentences
    def __init__(self, lhs, rhs):
        self.lhs = lhs
        self.rhs = rhs


class OrGroup:
    def __init__(self):
        self.expressions = []


class Sentence:
    def __init__(self):
        self.objects = []
        self.object_types = []

    def append_object(self, t_object, object_type):
        self.objects.append(t_object)
        self.object_types.append(object_type)

    def remove_object_at_index(self, index):
        self.objects.remove(index)
        self.object_types.remove(index)

    def insert_object_at_index(self, t_object, object_type, index):
        self.objects.insert(index, t_object)
        self.object_types.insert(index, object_type)

    def __hash__(self):
        t_str = ""
        for obj in self.objects:
            t_str = t_str + obj
        return hash(t_str)

    def __eq__(self, other):
        return (self.__hash__()) == (other.__hash__())

    def __ne__(self, other):
        # Not strictly necessary, but to avoid having both x==y and x!=y
        # True at the same time
        return not (self == other)


class BracketGroup:
    def __init__(self, expression):
        self.expression = expression
