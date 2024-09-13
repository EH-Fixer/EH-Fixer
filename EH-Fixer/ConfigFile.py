workingDir = ""
RetDataSetDir = "RetDataSet/"

TH_d = 0.4
TH_e = 3
Th_p = 5

baseUrl = ""
apiKey = ""
ThreadLengthThreshold = 5
varSavePath = workingDir+"/SaveVar/"
projectSavePath = workingDir+"/ProjectInfo/"


SharedFoldPath = "FoundThread/"
checkConditionSavePath = workingDir+"/CheckConditionInfo/"
cmdRun = True
OnlyReadFlag = True
CallPathDiff = False
LogEHRRFlag = True
DetailAnalysis = True
setGlobalContext = True#flag use for cross-project learn
loadAllVarFlag = False#flag use for cross-project learn
MeteTrainMinGroupNum = 2
VarTrainMinGroupNum = 2
TestDataGenFlag = True
FindedBugPath = ""
CurStage = ""#Learning, Detection
pInfoList = []

TargetFlag = "Linux"
#TargetFlag = "Others"

projectBasicPath = workingDir + "/Test/"

def SetConfig(pInfo):
    global pInfoList
    pInfoList = pInfo

def ConfigFunc():
    global projectBasicPath
    BasicPath = "StructInfo/"
    #fileTypes = ["c", "cc", "h"]
    fileTypes = ["c", "h"]

    pPathList, patternListList = SigProjectDivide(pInfoList)
    projectPathList = []
    for i in pPathList:
        projectPathList.append(projectBasicPath + i)
    return pPathList, projectPathList, patternListList, BasicPath, fileTypes, TH_score

def SigProjectDivide(pInfoList):
    pPathList = []
    patternListList = []
    for sigpi in pInfoList:
        pPathList.append(sigpi[0])
        patternListList.append(sigpi[1:])
    return pPathList, patternListList