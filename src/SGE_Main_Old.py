if __name__ == '__main__':
    import src.SGE_OLD as SGE

    # sge_iterations = 60
    sge_iterations = 60
    test_iterations = 5

    success_save = []
    iterations_save = []
    sge = SGE.SGE_OLD("NumberIO")
    sge.population_size = 100
    sge.recursion_max = 3
    sge.read_bnf_file()
    sge.read_supplementary_files()
    for t in range(0, test_iterations):
        print("test %d" % t)
        bestResults = sge.run_iterations(sge_iterations)
        success_save.append(bestResults[2])
        iterations_save.append(bestResults[3])
        # print("\n\n\n\n\n\n\n\n\nPrinting Best Results\n\n")
        # for i in range(0, 5):
        #     phen = sge.translateSeqToPhenotype(bestResults[0][i])[0][0]
        #     code = sge.translateObjectsIntoCode(phen)
        #     print(code)
        #     print(str(bestResults[1][i]))
        #     print("\n\n")

    with open("out.csv", "w") as fp:
        for t in range(0, test_iterations):
            t_str = str(success_save[t]) + "," + str(iterations_save[t]) + "\n"
            fp.write(t_str)