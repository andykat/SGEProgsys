import random
import copy
import math
from enum import Enum
from collections import defaultdict


class SGE_OLD:

    def __init__(self, file_name):
        self.file_name = file_name
        self.rules = {}
        self.non_terminals = []
        random.seed()
        self.population_size = 100
        self.genotype_max = 99999999  # maximum value for each integer
        self.genotype_min = 0  # minimum value for each integer

        self.tournament_k = 5  # number of entrants for each tournament
        self.tournament_p = 0.8  # probability of selecting winner
        self.top_performing_carry = 3  # number of top performing sequences from previous population carried over

        self.gene_mutation_chance = 0.25  # chance that a gene mutates
        self.average_best_fitness = []
        self.average_best_fitness_N = 5

        self.recursion_max = 20  # level of recursion

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
        Reads the grammar file and converts it into a grammar data structure
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
                # rhs = t_split[1].strip().replace("\n", "")
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
                                    sub_string = obj_copy[start_index: end_index + 1]
                                    obj_copy = obj_copy[end_index + 1:]
                                    s.append_object(sub_string, TerminalType.NONTERMINAL)

                            else:
                                obj = obj.replace("\\n", "\n  ")
                                s.append_object(obj, TerminalType.TERMINAL)

                    o.expressions.append(s)

                self.rules[lhs] = Production(lhs, o)
                if count == 0:
                    self.final_nonterminal = lhs
                    count += 1

        self.process_grammar_recursion()
        for rule_lhs, rule in self.rules.items():
            print("lhs:" + rule_lhs)

            for expression in rule.rhs.expressions:
                for ob in expression.objects:
                    print(ob, end='')
                print("|", end='')
            print("\n")

        # for lhs, rule in self.rules.items():
        #     self.non_terminals.append(lhs)

        self.count_references()
        self.calculate_expansions()

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
                        new_lhs = self.append_level_to_nonterminal(lhs, i - 1)
                    new_nt = self.append_level_to_nonterminal(lhs, i)
                    if i < self.recursion_max - 1:
                        for j in range(0, len(or_group_deep_copy.expressions)):
                            expression = or_group_deep_copy.expressions[j]
                            for k in range(0, len(expression.objects)):
                                if expression.objects[k] == lhs and expression.object_types[
                                    k] == TerminalType.NONTERMINAL:
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
                                if expression.objects[k] == lhs and expression.object_types[
                                    k] == TerminalType.NONTERMINAL:
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
                                    if expression.objects[k] == lhs and expression.object_types[
                                        k] == TerminalType.NONTERMINAL:
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
                                    if new_expression.objects[new_exp_index] == lhs and new_expression.object_types[
                                        new_exp_index] == TerminalType.NONTERMINAL:
                                        new_expression.objects.pop(new_exp_index)
                                        new_expression.object_types.pop(new_exp_index)
                                        for l in range(0, len(replace_exp.objects)):
                                            new_expression.objects.insert(new_exp_index + l, replace_exp.objects[l])
                                            new_expression.object_types.insert(new_exp_index + l,
                                                                               replace_exp.object_types[l])
                                    else:
                                        new_exp_index += 1
                                new_or_group.expressions.append(new_expression)

                    self.rules[new_lhs] = Production(new_lhs, new_or_group)
                    self.non_terminals.append(new_lhs)

    @staticmethod
    def append_level_to_nonterminal(stri, level):
        position = stri.find('>')
        newstr = ""
        if position < 0:
            print("error: > not found in nonterminal")
        else:
            newstr = stri[:position] + "lvl" + str(level) + stri[position:]

        return newstr

    def count_references(self):
        """
        counts the max number of times a left hand sided terminal can expand into each nonterminal
        :return:
        """
        self.references_count = {}

        for refnt in self.non_terminals:
            # create dictionary for lhs nonterminal
            self.references_count[refnt] = {}
            # for lhs, rule in self.rules.items():
            #     # look for the rule where refnt is expanded
            #     if rule.lhs == refnt:
            rule = self.rules[refnt]
            for exp in rule.rhs.expressions:
                # creates dictionary for rhs nonterminals
                count = {}
                for i in range(0, len(exp.objects)):
                    if exp.object_types[i] == TerminalType.NONTERMINAL:
                        if exp.objects[i] in count:
                            count[exp.objects[i]] += 1
                        else:
                            count[exp.objects[i]] = 1

                for key in count.keys():
                    if key in self.references_count[refnt]:
                        if count[key] > self.references_count[refnt][key]:
                            self.references_count[refnt][key] = count[key]
                    else:
                        self.references_count[refnt][key] = count[key]
        # print(self.references_count)

    # counts the number of expansions per nonterminal
    def calculate_expansions(self):
        # count of each nonterminal
        terminal_count = {}
        self.gene_expansion_count = {}
        # print("\n\n references count \n\n")
        # print(json.dumps(self.references_count, indent=3))
        for refnt in self.non_terminals:
            if refnt == self.final_nonterminal:
                terminal_count = self.references_count[refnt]
                self.gene_expansion_count[refnt] = 1
            else:
                # number of times refnt is expanded
                refnt_count = terminal_count[refnt]
                self.gene_expansion_count[refnt] = refnt_count

                # for each nt that refnt references, we add the
                # product of the referencecount for nt and the number of times refnt is expanded
                # to the terminal Count
                for nt in self.references_count[refnt].keys():
                    if nt in terminal_count:
                        terminal_count[nt] += self.references_count[refnt][nt] * refnt_count
                    else:
                        terminal_count[nt] = self.references_count[refnt][nt] * refnt_count
        # print(self.gene_expansion_count)

    def initialize_population(self):
        self.currentPopulation = []
        self.fitness = []
        for i in range(0, self.population_size):
            gene_dict = {}
            for key in self.gene_expansion_count:
                # genotypeMaxLength = self.gene_expansion_count[key]
                gene_dict[key] = []
                for j in range(0, 1):
                    gene_dict[key].append(self.random_genotype())
            self.currentPopulation.append(gene_dict)
            self.fitness.append(0)

    def random_genotype(self):
        return random.randint(self.genotype_min, self.genotype_max)

    def recombination(self, parents, nonterminal_counts):
        child = {}
        mutated_parents = []

        for parent in parents:
            mutated_parents.append(copy.deepcopy(parent))
        # mutate genes
        for i in range(0, len(mutated_parents)):
            mutated_parents[i] = self.mutate_parent(mutated_parents[i], nonterminal_counts[i])
        for nt in self.non_terminals:
            rand_n = random.randint(0, 1)
            child[nt] = copy.deepcopy(mutated_parents[rand_n][nt])
        return child

    def mutate_parent(self, parent, nonterminal_count):
        for nt in self.non_terminals:
            chance = random.uniform(0, 1)
            if chance < self.gene_mutation_chance:
                if nonterminal_count[nt] > 0:
                    rand_index = random.randint(0, nonterminal_count[nt] - 1)
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

            child[0][nt] = child[0][nt] + copy.deepcopy(mutated_parents[rand_n][nt])[:crossover_point]
            child[0][nt] = child[0][nt] + copy.deepcopy(mutated_parents[other_n][nt])[crossover_point:]
            child[1][nt] = child[1][nt] + copy.deepcopy(mutated_parents[other_n][nt])[:crossover_point]
            child[1][nt] = child[1][nt] + copy.deepcopy(mutated_parents[rand_n][nt])[crossover_point:]

        return child

    def mutation(self, seq):
        for nt in self.non_terminals:
            chance = random.uniform(0, 1)
            if chance < self.gene_mutation_chance:
                rand_index = random.randint(0, len(seq[nt]) - 1)
                seq[nt][rand_index] = self.random_genotype()
        return seq

    def translate_seq_to_phenotype(self, genes, remove_nonterminals=True):
        cur_objects = []
        curobject_types = []
        cur_objects.append(self.final_nonterminal)
        curobject_types.append(TerminalType.NONTERMINAL)
        nonterminal_count = {}
        nonterminal_index_start = 0
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
            # replace non terminal with new expression
            cur_objects.pop(nonterminal_index)
            curobject_types.pop(nonterminal_index)
            for i in range(0, len(expression.objects)):
                cur_objects.insert(nonterminal_index + i, expression.objects[i])
                curobject_types.insert(nonterminal_index + i, expression.object_types[i])

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
            selected.append(random.randint(0, self.population_size - 1))
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
        nonterminal_counts = [self.population_nonterminal_count[parent0index],
                              self.population_nonterminal_count[parent1index]]
        # nonterminal_counts.append()
        # nonterminal_counts.append()
        children = self.recombination_cross(parents, nonterminal_counts)
        return children

    def run_iterations(self, iterations):
        self.initialize_population()
        self.average_best_fitness = []
        # run the iterations
        iteration_count = 0
        success_flag = False
        for i in range(0, iterations):
            if i % 10 == 0:
                print("iteration: " + str(i))
            iteration_count += 1
            success_flag = self.step()
            if success_flag:
                break

        # get highest performers
        for i in range(0, self.population_size):
            seq = self.currentPopulation[i]
            phen = self.translate_seq_to_phenotype(seq, remove_nonterminals=True)[0][0]
            code = self.translate_objects_into_code(phen)
            self.fitness[i] = self.number_io_fitness(code)
            # get the top performing sequences

        self.fitness_indicies = []
        for i in range(0, self.population_size):
            self.fitness_indicies.append([i, self.fitness[i]])

        sorted(self.fitness_indicies, key=lambda x: x[1], reverse=True)
        self.highest_performers = []
        self.highest_fitnesses = []
        number_of_top_performers = 5

        for i in range(0, number_of_top_performers):
            self.highest_performers.append(self.currentPopulation[self.fitness_indicies[i][0]])
            self.highest_fitnesses.append(self.fitness_indicies[i][1])
        # print(self.highest_fitnesses[0])
        return [self.highest_performers, self.highest_fitnesses, success_flag, iteration_count]

    def step(self):
        self.population_nonterminal_count = []
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
            self.fitness[i] = self.number_io_fitness(code)

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
        # for i in range(0, 3):
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

        return flag

    @staticmethod
    def translate_objects_into_code(objects):
        code = ""
        for s in objects:
            code += s
        return code

    def number_io_fitness(self, code):
        final_code = self.helper_code.replace("<insertCodeHere>", code)
        error = 0.0
        try:
            loc = {}
            exec(final_code, loc, loc)
            error = loc['quality']
        except Exception:
            print("Error in code")
            error = 9999999

        return -error

    @staticmethod
    def calc_min(a, b):
        if a < b:
            return a
        return b


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