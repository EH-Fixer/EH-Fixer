from EHFixer import runTest

pinfoList = []
bugLocation = []

runTest(0, pinfoList, "Contruct EHDB")

for bugPath, lineNumber in bugList():
    EHFix(pinfoList[0][0], bugPath, lineNumber)