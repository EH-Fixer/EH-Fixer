import datetime

from DataStructure import EHThreadList, EHBInfo, CodeAnalyzer, loadEHSet
import pickle, copy
from ReturnAndFunc import is_log_function, add_to_set_with_count, final_process, determine_action, loadSavedAnaSet
from tools import save_variable, load_variable
from ConfigFile import RetDataSetDir, sampleNum, ThreadLengthThreshold, SharedFoldPath, TestDataSetDir, projectBasicPath, TargetFlag
import random
from TemptSave import load_variables
from collections import Counter
from itertools import groupby
from FIxAgent import PatchGenerate, oneshotPrompt
from CheckAgent import CheckAgent
import re
from ExcelWriterTool import write_to_excel
from cluster import clust
overAllStopIterate = 0
from EHFixDataConstruct import apply_changes
AllEHThread = EHThreadList()
FuncEHThreadInter = {}
FuncEHThreadProcessedSet = set()
UpThread = {}
FuncEHLog = set()
HandledFuncDict = {}
data2RR = []
resRepGlobListFlat = []
codeRepList = []
resRepMapInfo = []
argMap = []
codes = []
non_added_indexes = []
canalyzer = CodeAnalyzer()
resLen = -1
nameAndIndex = {}
funcDefInfoDict = {}#key is funcName, value is [funcType, callList]
funcEHCodeMap = {}

summmaryList = []#NLP summary corresponding to summaryIndex of funcEHCodeMap[funcName][5]
handlingList = []#corresponding to summmaryList. recording the NLP summary of the EH action of EHCodes(in funcEHCodeMap)
handledSumDict = {}#handledSumDict[blamefunc] = [summary index correspond to code of four strategies].

funcHandledMap = {}
ErrorCodeMap = {}

Type2CleanUp = {}
returnBackGroundPrompt = ""

handledFuncMap = {}
callerGraph = {}
callGraph = {}
thirdPartyCallerGraph = {}
nameListForReach = []
funcCodeDict = {}
nameSet = set()
provSet = set()

rewriteDict = {}
reRewriteDict = {}

def form_file_EH():
    global funcEHCodeMap, handledFuncMap, canalyzer, nameListForReach
    #marker = [0 for _ in nameListForReach]
    for i, funcs in enumerate(canalyzer.funcList):
        for funcName in funcs:
            #marker[funcName] = 1
            if (funcName in funcEHCodeMap):
                for ehi, sigEHList in enumerate(funcEHCodeMap[funcName]):
                    if (len(sigEHList)>4):
                        break
                    codes, rflag, fList, blameFunc = sigEHList
                    codes = codes.replace("\\n", "\n")
                    type = determine_action(fList)
                    if (rflag and type<4):
                        type += 1
                    if (blameFunc != None):
                        if (blameFunc not in handledFuncMap):
                            handledFuncMap[blameFunc] = [[], [], [], [], []]
                        handledFuncMap[blameFunc][type].append([funcName, codes])
                    tp = FormLearningPrompt(blameFunc, funcName)
                    if (tp!=None):
                        canalyzer.typeCodeList[i][type].append(tp)
                    funcEHCodeMap[funcName][ehi].append(type)

def SaveCode2Path(projectName):
    global canalyzer
    canalyzer.optSearch()
    save_variable(canalyzer, RetDataSetDir + projectName + "canalyzer.pickle")

def LoadCode2PathFromFile(projectName):
    global canalyzer
    canalyzer = load_variable(RetDataSetDir + projectName + "canalyzer.pickle")

def LoadCode2Path(cList, fset, ftDict, p):
    global canalyzer
    canalyzer.addSig(cList, fset, ftDict, p)

def save_AllEHThread_to_file(file_path):
    global AllEHThread
    with open(file_path, 'wb') as file:
        pickle.dump(AllEHThread, file)

def load_AllEHThread_from_file(file_path):
    global AllEHThread
    with open(file_path, 'rb') as file:
        AllEHThread = pickle.load(file)
    print("AllEHThread load", len(AllEHThread.threads))

def LoadNameList(nindex, fd):
    global nameAndIndex, funcDefInfoDict
    nameAndIndex = nindex
    funcDefInfoDict = fd

def preprocess_codes():
    global codes, non_added_indexes
    non_added_indexes = []
    in_added_section = False

    for i, code in enumerate(codes):
        if code.startswith("---------GOTO----------\n"):
            in_added_section = True
        elif code.endswith("\n---------GOTO END----------\n"):
            in_added_section = False
        elif not in_added_section and "*__ADDED__*" not in code:
            non_added_indexes.append(i)
def LoadData2RR(d2rr, rrgflat, crList, rrmap, am, cs):
    global data2RR, resRepGlobListFlat, codeRepList, resRepMapInfo, argMap, codes, resLen, non_added_indexes
    data2RR = d2rr
    resRepGlobListFlat = rrgflat
    codeRepList = crList
    resRepMapInfo = rrmap
    argMap = am
    codes = []
    for ind, sigc in enumerate(cs):
        codes.append(sigc.strip())

    resLen = len(resRepGlobListFlat)

    preprocess_codes()

def ForwardSearch(pos):
    global resRepMapInfo
    rn = len(resRepGlobListFlat)
    curList = resRepMapInfo[pos]
    ans = []
    while(curList!=[]):
        newList = []
        for sigc in curList:
            if (sigc<rn and resRepGlobListFlat[sigc][0] == "Assign"):
                #_, _, _, left, rightList, _ = resRepGlobListFlat[curPos]
                if (len(resRepGlobListFlat[sigc][4])==1):
                    newList.extend(resRepMapInfo[sigc])
            else:
                ans.append(sigc)
        curList = newList
    return ans

def HavePostive(pos):
    global argMap
    tarList = argMap[pos]
    ans = []
    tNum = len(tarList)
    for i in range(tNum):
        if (tarList[i]>=0):
            ans.append(i)
    return ans

def UpHandledByFunc(targetPos, funcName):
    global resRepGlobListFlat, argMap, resRepMapInfo
    emptyThreadList = EHThreadList()
    newThreadList = HandleByFunc(targetPos, None, funcName, None, emptyThreadList)
    if (newThreadList != None):
        if (funcName not in UpThread):
            UpThread[funcName] = newThreadList
        else:
            UpThread[funcName].merge(newThreadList)

def UpThreadObtain(funcName):
    global UpThread, resRepGlobListFlat, codeRepList, argMap, resRepMapInfo
    #print("UpThreadObtain", funcName)
    rNum = len(resRepGlobListFlat)
    mapNum = len(resRepMapInfo)
    argNum = mapNum-rNum
    #print("rNum and argNum", rNum, argNum)
    for i in range(argNum):
        curPos = rNum+i
        #print("curPos", curPos)
        UpHandledByFunc(curPos, funcName)
        #LinkedFuncCheck(resRepGlobListFlat, argMap, resRepMapInfo, funcName, curPos)
        targetPosList = ForwardSearch(curPos)
        #print("targetPosList", targetPosList)
        for sigt in targetPosList:

            if (resRepGlobListFlat[sigt][0]=="CHECK" or resRepGlobListFlat[sigt][0]=="Assert CHECK"):
                temptInfo = BranchDetail(sigt, None, None, funcName)
                if (temptInfo == None):
                    #print("Wired, not suppose to happen during upSearch")
                    continue
                curEHInfo, start, end, rflag = temptInfo
                curEHInfo.argPos = i
                newEHThreadList = EHThreadList()
                newEHThreadList.append_EHBInfo(curEHInfo)
                if (funcName not in UpThread):
                    UpThread[funcName] = newEHThreadList
                else:
                    UpThread[funcName].merge(newEHThreadList)

def CheckedByFunc(pos):
    global UpThread, argMap, resRepMapInfo, resRepGlobListFlat
    #print("CheckedByFunc", pos, argMap[pos])
    targetArgMap = argMap[pos]
    tn = len(targetArgMap)
    for i in range(tn):
        if (targetArgMap[i] >= 0):
            funcPos = resRepMapInfo[pos][i]
            if (resRepGlobListFlat[funcPos][0] == "FuncCall"):
                checkedFunc = resRepGlobListFlat[funcPos][1].name
                if (checkedFunc in UpThread):
                    checkThreadList = UpThread[checkedFunc].check_argpos(targetArgMap[i])
                    if (checkThreadList!=None):
                        return checkedFunc, checkThreadList
            #else:
            #    print("Debug Wrong", targetArgMap[i], resRepGlobListFlat[funcPos])
    return None

def FuncEHLogInit():
    global FuncEHLog
    FuncEHLog = set()

def saveFuncEHLog():#方便记录
    global FuncEHLog
    return FuncEHLog

def loadFuncEHLog(flog):
    global FuncEHLog
    FuncEHLog = flog

def ThreadListAddCheck(newEHThreadList, rflag, funcName):
    global AllEHThread, FuncEHThreadInter, FuncEHLog
    #print("ThreadListAddCheck", funcName, newEHThreadList)
    if (rflag):
        #print("ThreadListAddCheck", funcName, newEHThreadList)
        if (funcName in FuncEHThreadInter):
            FuncEHThreadInter[funcName].merge(newEHThreadList)
        else:# 函数还没存EH
            FuncEHThreadInter[funcName] = newEHThreadList
    else:
        AllEHThread.merge(newEHThreadList)

def RestTreadObtain():
    global FuncEHThreadInter, FuncEHThreadProcessedSet, AllEHThread
    print("RestTreadObtain Start")
    for key, value in FuncEHThreadInter.items():
        if key not in FuncEHThreadProcessedSet:#value is a data type of "EHList"
            AllEHThread.merge(value)
    print("RestTreadObtain End")

def FuncHandleByCheck(curPos, targetPos, funcName, calleeFuncName):
    global FuncEHThreadInter, FuncEHThreadProcessedSet, FuncEHLog, resRepGlobListFlat, codeRepList, HandledFuncDict
    #print("FuncHandleByCheck", funcName, calleeFuncName)
    if (funcName not in HandledFuncDict):
        HandledFuncDict[funcName] = set()
        HandledFuncDict[funcName].add(calleeFuncName)
    else:
        if (calleeFuncName not in HandledFuncDict[funcName]):
            HandledFuncDict[funcName].add(calleeFuncName)
    if targetPos not in FuncEHLog:
        #print("FuncHandleByCheck BranchDetail", funcName, calleeFuncName)
        #print("FuncHandleByCheck targetPos", resRepGlobListFlat[targetPos])
        #print("FuncHandleByCheck curPos", resRepGlobListFlat[curPos])
        temptBInfo = BranchDetail(targetPos, curPos, calleeFuncName, funcName)
        #print("FuncHandleByCheck temptBInfo", funcName, calleeFuncName, temptBInfo)
        if (temptBInfo == None):
            return
        curEHInfo, start, end, rflag = temptBInfo
        newEHThreadList = EHThreadList()
        #print("FuncEHThreadInter", calleeFuncName, FuncEHThreadInter.keys())

        if (calleeFuncName in FuncEHThreadInter):
            #print("FuncEHThreadInter[calleeFuncName]", FuncEHThreadInter[calleeFuncName])
            FuncEHThreadProcessedSet.add(calleeFuncName)
            newEHThreadList = copy.deepcopy(FuncEHThreadInter[calleeFuncName])
        #else:
        #    print(f"{calleeFuncName} not in FuncEHThreadInter")
        newEHThreadList.append_EHBInfo(curEHInfo)
        FuncEHLog.add(targetPos)
        #print("funcName calleeFuncName", funcName, calleeFuncName)
        #print("FuncHandleByCheck", "funcName", funcName, "calleeFuncName", calleeFuncName)
        ThreadListAddCheck(newEHThreadList, rflag, funcName)
        #print("ThreadListAddCheck End")
    #else:
        #print("Error: duplicate search")

def HandleByFunc(targetPos, curPos, funcName, calleeFuncName, upperThreadList):
    global resRepGlobListFlat, argMap, resRepMapInfom, resLen
    tempt = CheckedByFunc(targetPos)
    if (tempt != None):
        handleFunction, handleThreadList = tempt
        if (targetPos<resLen):
            curEHInfo = FuncDetail(targetPos, curPos, calleeFuncName, funcName)
            upperThreadList.append_EHBInfo(curEHInfo)
        upperThreadList.concatenate(handleThreadList)
        return upperThreadList
    return None

def HandledByReturn(returnPos, funcCallPos, funcName, calleeFuncName):#Simply return the function
    #print("HandledByReturn")
    global FuncEHLog, FuncEHThreadProcessedSet

    if (funcName not in HandledFuncDict):
        HandledFuncDict[funcName] = set()
        HandledFuncDict[funcName].add(calleeFuncName)
    else:
        if (calleeFuncName not in HandledFuncDict[funcName]):
            HandledFuncDict[funcName].add(calleeFuncName)

    if returnPos not in FuncEHLog:
        FuncEHLog.add(returnPos)
        curEHInfo = FuncDetail(returnPos, funcCallPos, calleeFuncName, funcName)
        newEHThreadList = EHThreadList()
        if (calleeFuncName in FuncEHThreadInter):
            #print("FuncEHThreadInter[calleeFuncName]", FuncEHThreadInter[calleeFuncName])
            FuncEHThreadProcessedSet.add(calleeFuncName)
            newEHThreadList = copy.deepcopy(FuncEHThreadInter[calleeFuncName])
        #else:
        #    print(f"{calleeFuncName} not in FuncEHThreadInter")
        newEHThreadList.append_EHBInfo(curEHInfo)
        #print("HandledByReturn", funcName, calleeFuncName)
        ThreadListAddCheck(newEHThreadList, True, funcName)

def FuncHandleByFunc(curPos, targetPos, funcName, calleeFuncName):
    #print("FuncHandleByFunc")
    global FuncEHThreadInter, FuncEHThreadProcessedSet, resRepGlobListFlat, argMap, resRepMapInfo, FuncEHLog, HandledFuncDict
    if (targetPos in FuncEHLog):
        return
    FuncEHLog.add(targetPos)
    '''if (funcName == "snd_es18xx_mixer"):
        print("FuncHandleByFunc snd_es18xx_mixer", funcName, calleeFuncName)
        print('FuncEHThreadInter[calleeFuncName]', len(FuncEHThreadInter[calleeFuncName].threads))
    if (funcName == "snd_ctl_new1"):
        print("FuncHandleByFunc snd_ctl_new1", funcName, calleeFuncName)'''
    '''print("FuncHandleByFunc", resRepGlobListFlat[targetPos])
    print("resRepMapInfo", resRepMapInfo[targetPos])
    print("argMap", argMap)
    rn = len(resRepGlobListFlat)
    for i in range(rn):
        print("resRepGlobListFlat", i, resRepGlobListFlat[i])
    for eachrr in resRepMapInfo[targetPos]:
        print("eachrr", resRepGlobListFlat[eachrr])'''
    newEHThreadList = EHThreadList()
    if (calleeFuncName in FuncEHThreadInter):
        FuncEHThreadProcessedSet.add(calleeFuncName)
        newEHThreadList = copy.deepcopy(FuncEHThreadInter[calleeFuncName])
    newEHThreadList = HandleByFunc(targetPos, curPos, funcName, calleeFuncName, newEHThreadList)
    if (newEHThreadList!=None):
        if (funcName not in HandledFuncDict):
            HandledFuncDict[funcName] = set()
            HandledFuncDict[funcName].add(calleeFuncName)
        else:
            if (calleeFuncName not in HandledFuncDict[funcName]):
                HandledFuncDict[funcName].add(calleeFuncName)
        #print("FuncHandleByFunc", "funcName", funcName, "calleeFuncName", calleeFuncName)
        ThreadListAddCheck(newEHThreadList, False, funcName)

def RRPos2CodePos(pos):
    global data2RR
    codePos = 0
    while (data2RR[codePos] <= pos):
        codePos += 1
    codePos -= 1
    return codePos

def RangeChange(s, e):
    global data2RR
    ns = data2RR[s]
    ne = None
    if (e+1<len(data2RR)):
        ne = data2RR[e+1]
    return ns, ne

def HaveReturn(targetPos, cPos, origns, origne):
    global resRepGlobListFlat, codes, codeRepList, data2RR, ErrorCodeMap, Type2CleanUp
    origne -= 1#origne is not in the branch
    #print("HaveReturn origns origne", origns, origne)
    s, e = RangeChange(origns, origne)
    #print("HaveReturn end e", e, resRepGlobListFlat[e])
    #print("data2RR", data2RR)
    #print("codes", codes)
    #print("new se", s, e)
    #print("cLen", len(codes), len(resRepGlobListFlat), len(data2RR))
    rFlag = False
    returnItem = None
    errorCode = None
    fList = []
    rrlen = len(resRepGlobListFlat)
    if e == None:
        e = rrlen
    elif e > rrlen:
        print("Wired", rrlen, len(codes), e)
        print("targetPos", targetPos, resRepGlobListFlat[targetPos])
        #print("cPos", codes[cPos])
        for j in range(s, min(len(resRepGlobListFlat), e+1)):
            print("sig code", j, resRepGlobListFlat[j])
        e = rrlen
    #print("HaveReturn", s, e)
    for i in range(s, e):
        #print("HaveReturn resRepGlobListFlat", resRepGlobListFlat[i])
        #if (resrepglobal[i][0] == "Return"):
        if (resRepGlobListFlat[i][0] == "Return"):
            #print("HaveReturn Test", resRepGlobListFlat[i], resRepGlobListFlat[i][1][0].norm[0][0])
            errorCode = ""


            if (resRepGlobListFlat[i][-1]!=[]):
                if (resRepGlobListFlat[i][1][0].norm[0][0] == "__HardCodedVar__"):
                    errorCode = resRepGlobListFlat[i][1][0].bList[0][0]
                elif("**_FUNC_CALL_**" in resRepGlobListFlat[i][1][0].norm[0][0]):
                    errorCode = resRepGlobListFlat[i][1][0].norm[0][0][15:]
            else:
                if (len(resRepGlobListFlat[i][1])>0):
                    if (resRepGlobListFlat[i][1][0].ArgType == "Arg"):
                        if (resRepGlobListFlat[i][1][0].itemTypeList[0][0] == "null"):
                            errorCode = "NULL"
                    else:
                        if ("**_FUNC_CALL_**" in resRepGlobListFlat[i][1][0].norm[0][0]):
                            errorCode = resRepGlobListFlat[i][1][0].norm[0][0][15:]
                        else:
                            print("Debug!:HaveReturn abnormal FuncCall", str(resRepGlobListFlat[i][1][0]))

                #print("Empty return", str(resRepGlobListFlat[i][1][0]))
            rFlag = True
            returnpos = 0
            while (data2RR[returnpos] <= i):
                returnpos += 1
            returnpos -= 1
            returnItem = codes[returnpos]
            #print("HaveReturn Return", returnItem)
            #returnItem =
        elif (resRepGlobListFlat[i][0] == "FuncCall"):
            funcName = resRepGlobListFlat[i][1].name
            #print("HaveReturn FuncCall", resRepGlobListFlat[i], funcName)

            fAList = resRepGlobListFlat[i][1].argList

            if (fAList!=None and len(fAList)>=1):
                for eachA in fAList:
                    if(eachA != None and len(eachA.norm)>=1):
                        curDataType = eachA.norm[0][0]
                        if (isinstance(curDataType, str)):
                            if (curDataType != "__HardCodedVar__"):
                                if (curDataType not in Type2CleanUp):
                                    Type2CleanUp[curDataType] = [funcName]
                                else:
                                    Type2CleanUp[curDataType].append(funcName)
            fList.append(funcName)
            is_log_function(codes[RRPos2CodePos(i)], funcName)
        elif (resRepGlobListFlat[i][0] == "CHECK" and i!=targetPos):
            #print("resRepGlobListFlat[i]", resRepGlobListFlat[i])
            if(i != s):
                return None
            else:
                if (len(resRepGlobListFlat[targetPos])>4):
                    start, e, es, end = resRepGlobListFlat[targetPos][3:7]
                    if (es!=None and es!=-1):
                        return None
    add_to_set_with_count(rFlag, fList)
    #print("errorCode!", errorCode)
    return rFlag, returnItem, errorCode, fList

def GetCodeSnippet(sPos, ePos):#get codes between [sPos, ePos]
    global codes, non_added_indexes
    cn = len(codes)
    if (sPos == cn):
        return None
    curi = sPos
    ansList = []
    if (ePos>=cn):
        ePos = cn
    while(curi<ePos):
        if "*__ADDED__*" not in codes[curi]:
            ansList.append(codes[curi])
        curi += 1
    return "\n".join(ansList)

def GetBlameCode(cPos):
    global codes, non_added_indexes
    cn = len(codes)
    if (cPos == cn):
        return -1, -1
    ans = codes[cPos]
    tarIndex = ans.rfind("*__ADDED__*")
    if (tarIndex != -1):
        ans = ans[tarIndex+len("*__ADDED__*"):]
    #print("GetBlameCode", GetBlameCode)
    occurence = sum(1 for i in non_added_indexes if i < cPos and codes[i] == ans) + 1
    return ans, occurence

def GetCurCode(cPos):
    global codes, non_added_indexes
    cn = len(codes)
    if(cPos==cn):
        return -1, -1
    ans = codes[cPos]
    #print("GetCurCode", cPos, ans)
    if "*__ADDED__*" in ans:
        for i in range(cPos+1, cn):
            if ("*__ADDED__*" not in codes[i]):
                ans = codes[i]
                #print("before ans", codes[cPos])
                #print("after ans", ans)
                break

    #occurence = codes[:cPos].count(ans) + 1
    occurence = sum(1 for i in non_added_indexes if i < cPos and codes[i] == ans) + 1
    '''if (occurence>1):
        print("GetCurCode occurence", occurence)
        print("GetCurCode", codes[cPos])
        print("GetCurCode", codes[:cPos])'''
    return ans, occurence

def FindCodeLineNumber(funcName, cPos, blamePos, endPos):
    global codes
    #print("FindCodeLineNumber")
    curCode, occurence = GetCurCode(cPos)
    blameCode = None
    blame_occurrence = None
    if (blamePos!=None):
        #blameCode, blame_occurrence = GetCurCode(blamePos)
        blameCode, blame_occurrence = GetBlameCode(blamePos)
        #print("FindCodeLineNumber", blamePos, blameCode)
    branchCode = None
    if (cPos!=None):
        branchCode, _ = GetCurCode(cPos)
    endCode = None
    end_occurrence = None
    if (endPos!=None):
        endCode, end_occurrence = GetCurCode(endPos)
    #print("endPos", endPos, endCode)
    BranchCodeSnippet = branchCode
    if (endPos!=None):
        BranchCodeSnippet = GetCodeSnippet(cPos, endPos)
        #print("endCode", endCode, end_occurrence)
    #print("curCode", curCode)
    #print("occurence", occurence)
    temptCodes, lineNumber, blameLineNumber, endLineNumber, funcPos, funEndPos, path = canalyzer.find_branchInfo_in_function(funcName, curCode, blameCode, endCode, occurence, blame_occurrence, end_occurrence)
    if endLineNumber!=None:
        endLineNumber -= 1
    '''if (endLineNumber != None and lineNumber!=None and endLineNumber<lineNumber):
        print("FindCodeLineNumber debug", funcName, endCode, end_occurrence, "Linenumber", endLineNumber, lineNumber)
        cnum = len(codes)
        print("non_added_indexes", non_added_indexes)
        for sigc in range(cnum):
            print("sigc", sigc, codes[sigc])'''
    #print("lineNumber, path", lineNumber, path)
    return temptCodes, lineNumber, blameLineNumber, endLineNumber, funcPos, funEndPos, path, blameCode, branchCode, BranchCodeSnippet

def BranchDetail(targetPos, blamePos, blameFunc, funcName):
    global resRepGlobListFlat, codeRepList, funcEHCodeMap, handledFuncMap, funcHandledMap, ErrorCodeMap, funcDefInfoDict
    '''print("BranchDetail targetPos", targetPos, resRepGlobListFlat[targetPos])
    if (blamePos!=None):
        print("BranchDetail blamePos", blamePos, resRepGlobListFlat[blamePos])'''
    cPos = RRPos2CodePos(targetPos)
    if (blamePos!=None):
        blamePos = RRPos2CodePos(blamePos)
        #print("RRPos2CodePos newblamePos", blamePos, resRepGlobListFlat[blamePos])

    #print("codeRepList", codeRepList[cPos])
    if(resRepGlobListFlat[targetPos][0]!="CHECK"):
        print("Debug. BranchDetail Wrong", resRepGlobListFlat[targetPos])
    start = -1
    end = -1
    if (len(resRepGlobListFlat[targetPos])<=4):
        start = cPos
        end = cPos
        return None
        #print("branch1", start, end)
    else:
        #print("Debug BranchDetail resRepGlobListFlat[targetPos]", len(resRepGlobListFlat[targetPos][1][0]), resRepGlobListFlat[targetPos][1][0][1])
        if (resRepGlobListFlat[targetPos][1][0][1] != "CMP"):
            return None
        start, e, es, end = resRepGlobListFlat[targetPos][3:7]
        #print("BranchDetail resRepGlobListFlat", resRepGlobListFlat[targetPos])
        if (end == -1 or end == None):
            end = e

    temptAns = HaveReturn(targetPos, cPos, start, end)
    #print("HaveReturn", temptAns)
    if (temptAns == None):
        return None
    rflag, returnItem, errorCode, fList = temptAns
    returnItem = errorCode#simply replace it
    temptCodes, checkCodeLine, blameCodeLine, endCodeLine, funcPos, funcEndPos, fpath, funcCode, branchCode, BranchCodeSnippet = FindCodeLineNumber(funcName, cPos, blamePos, end)
    #print("funcCode", funcCode)
    #print("Debug Info", targetPos, blamePos, blameFunc, funcName)
    '''if (temptCodes == None):
        if("--GOTO" not in codes[end] and "---GOTO----" not in codes[cPos]):
            print("BranchDetail Wrong: temptCodes None", funcName, fpath, checkCodeLine)#这个通常是由于Goto导致的
    else:'''
    if (temptCodes!=None):
        if (endCodeLine!=None and checkCodeLine!=None and endCodeLine<checkCodeLine):#一些极端情况下，tree-sitter的分析，会导致endLine比checkCodeLine还小，这种情况舍弃掉
            return None
        if (errorCode!=None):
            if (errorCode not in ErrorCodeMap):
                ErrorCodeMap[errorCode] = [temptCodes]
            else:
                ErrorCodeMap[errorCode].append(temptCodes)
        if (funcName not in funcEHCodeMap):
            funcEHCodeMap[funcName] = [[temptCodes, rflag, fList, blameFunc]]
            if (blameFunc!=None):
                if (funcName not in funcHandledMap):
                    funcHandledMap[funcName] = set()
                    funcHandledMap[funcName].add(blameFunc)
                else:
                    funcHandledMap[funcName].add(blameFunc)
        else:
            funcEHCodeMap[funcName].append([temptCodes, rflag, fList, blameFunc])
            if (blameFunc!=None):
                if (funcName not in funcHandledMap):
                    funcHandledMap[funcName] = set()
                    funcHandledMap[funcName].add(blameFunc)
                else:
                    funcHandledMap[funcName].add(blameFunc)
    funcT = None
    if (funcName in funcDefInfoDict):
        funcT = funcDefInfoDict[funcName][1]
    else:
        print(f"Warning: {funcName} not in funcDefInfoDict")
    return EHBInfo(rflag, start, end, funcT, funcName, funcPos, funcEndPos, checkCodeLine, blameCodeLine, endCodeLine, blameFunc, fpath, funcCode, branchCode, BranchCodeSnippet, fList, returnItem), start, end, rflag

def FuncDetail(targetPos, blamePos, blameFunc, funcName):
    cPos = RRPos2CodePos(targetPos)
    if (blamePos!=None):
        blamePos = RRPos2CodePos(blamePos)
    _, checkCodeLine, blameCodeLine, _, funcPos, funcEndPos, fpath, funcCode, branchCode, BranchCodeSnippet = FindCodeLineNumber(funcName, cPos, blamePos, None)
    funcT = None
    if (funcName in funcDefInfoDict):
        funcT = funcDefInfoDict[funcName][1]
    else:
        print(f"Warning: {funcName} not in funcDefInfoDict")
    return EHBInfo(True, cPos, cPos, funcT, funcName, funcPos, funcEndPos, checkCodeLine, blameCodeLine, None, blameFunc, fpath, funcCode, branchCode, BranchCodeSnippet, None, None)

def EHBrachStore(targetPos, funcName):
    global FuncEHThreadInter, FuncEHLog, resRepGlobListFlat, codeRepList
    #print("EHBrachStore", funcName, resRepGlobListFlat[targetPos])
    #if (funcName == "page_ext_get"):
    #    print("EHBrachStore FuncEHLog", FuncEHLog)
    if targetPos not in FuncEHLog:
        #if (funcName == "page_ext_get"):
        #    print("Add branch", resRepGlobListFlat[targetPos])
        FuncEHLog.add(targetPos)
        temptEHInfo = BranchDetail(targetPos, None, None, funcName)
        if (temptEHInfo == None):
            return
        curEHInfo, start, end, rflag = temptEHInfo
        newEHThreadList = EHThreadList()
        newEHThreadList.append_EHBInfo(curEHInfo)
        #print("EHBrachStore ThreadListAddCheck", funcName, rflag, newEHThreadList)
        #if (funcName == "snd_es18xx_mixer" or funcName == "snd_ctl_new1"):
        #    print("EHBrachStore func", funcName)
        #print("EHBrachStore", funcName)
        ThreadListAddCheck(newEHThreadList, rflag, funcName)

def print_eh_thread_list_dict(header, eh_thread_list_dict):

    print(header)
    for func_name, eh_thread_list in eh_thread_list_dict.items():
        print(f"Function: {func_name}")
        print(eh_thread_list)
        print()

def ShowData(projectName):
    global AllEHThread, FuncEHThreadInter, UpThread, FuncEHLog, funcHandledMap, funcEHCodeMap, ErrorCodeMap, Type2CleanUp, funcCodeDict
    AllEHThread.dup_remove()
    AllEHThread.write_to_file(projectName+"_FoundThread.txt")
    save_AllEHThread_to_file(RetDataSetDir+projectName+"_AllEHThread.pickle")
    save_variable(funcEHCodeMap, RetDataSetDir+projectName+"_funcEHCodeMap.pickle")

    save_variable(HandledFuncDict, RetDataSetDir+projectName+"_HandledFuncDict.pickle")
    save_variable(funcHandledMap, RetDataSetDir + projectName + "_funcHandledMap.pickle")
    save_variable(ErrorCodeMap, RetDataSetDir + projectName + "_ErrorCodeMap.pickle")
    save_variable(Type2CleanUp, RetDataSetDir + projectName + "_Type2CleanUp.pickle")
    final_process(projectName)

def GetCode(tarPos):
    global codes
    return codes[tarPos]

def FormRelatedCodeMap(projectName):
    global funcEHCodeMap, canalyzer, handledFuncMap, funcCodeDict
    LoadCode2PathFromFile(projectName)
    loadSavedAnaSet(projectName)
    funcEHCodeMap = load_variable(RetDataSetDir + projectName + "_funcEHCodeMap.pickle")
    funcCodeDict = load_variable(RetDataSetDir + projectName + "_funcCodeDict.pickle")
    print("funcCodeDict", len(funcCodeDict.keys()))

    form_file_EH()
    SaveCode2Path(projectName)
    save_variable(funcEHCodeMap, RetDataSetDir + projectName + "_funcEHCodeMap.pickle")
    save_variable(handledFuncMap, RetDataSetDir + projectName + "_handledFuncMap.pickle")


def FormRetrivalDataSet(projectName):
    global AllEHThread
    print("FormRetrivalDataSet", projectName)
    AllEHThread.FuncRelatedThread(RetDataSetDir+projectName+"funcRelatedThread.pickle")#将funcRelatedThread存起来，这里记录了函数与Thread之间的map关系
    FormRelatedCodeMap(projectName)

severity_descriptions = [
        "logging the error only",
        "logging the error and terminating the program",
        "executing cleanup functions only",
        "executing cleanup functions and terminating the program",
        "completely killing the entire system"
    ]


globalPromptStart = "Fixing error handling bugs needs to consider two aspects: the severity of the error, and whether the error affects other functions."
errorSeverityPrompt = "The severity of the error determines how the error should be handled: some errors don't need to be handled, some just need to be logged, some need to perform a specific cleanup function, and some need to end the current function."
errorPropargationPrompt = "Errors usually affect other functions via data/control flow. Errors need to return an error code if the error affects other functions, then error handling needs to return an error code."
OutputFormatPrompt = "Please follow the pseudo-code below to generate the answer:\n\
if ({Where the error occurred} needs error handling){\n\
Output (#NeedEH:Y)\n\
if (need to log){\n\
Output (#LogInfo: please describe the error)\n\
}\n\
if (cleanup function is required){\n\
Output (#ResourceNeedFree: list the resources that need to be freed, split by \",\")\n\
}\n\
if (affects other functions) {\n\
Output (#ErrorCode: error code to be returned)\n\
Output (#AffectedFunc: list the affected functions, split by \",\")\n\
}\n\
}\n\
else{\n\
Output (#NeedEH:N)\n\
}"

def generate_prompt_for_error_handling(collectedCodeList):

    prompt = ""

    for i, code_snippets in enumerate(collectedCodeList):
        if code_snippets:
            prompt += f"Strategy {i + 1} ({severity_descriptions[i]}):\n"
            for snippet in code_snippets:

                prompt += f"- {snippet}\n"
    return prompt

def formPrompt(errorFunction, errorLocatedFunction, callGraphDescribe, contextCode, SameFileCode, OtherEH):
    ContextPrompt = f"In , the {errorFunction} in {errorLocatedFunction} is missing error handling.\n\
    This function comes from a software project I recently wrote, please help me fix this error-handling bug, and return fixed functions.\n\
    Note that: \n\
    1. The error could propagate to multiple functions through return values;\n\
    2. Different software systems have varies handling strategies, please refer to the existing error-handling code snippets we provided.\n\
    3. Existing error-handling code snippets can be considered as the most appropriate, unless there are new error code that previously cannot be handled.\n\
    4. The handling of the error in each function should consider its severity and its context and chose the most suitable handling strategy.\n\
    5. Please concentrate on the error generated by {errorFunction} and its propagation only.\n\
    6. Use only functions and error codes included in the input.\n\
    7. Don't generate pseudo-code.\n\
    8. Only output the fix in the form of an patch, and add \"------Patch Start------\" and \"------Patch End------\" in the front and the back of the patch, respectively.\n\
    Here is the call graph of the {errorLocatedFunction}:\n {callGraphDescribe}\n\
    Here is the source code of relevant function:\n {contextCode}"
    OtherHandlingPrompt = f"The following is the error handling for the {errorFunction} in another location:\n{OtherEH}"
    SameFileCodePrompt = f"The following are other error handling in the same module:\n{SameFileCode}"
    return ContextPrompt, SameFileCodePrompt, OtherHandlingPrompt

def GetSameFuncHandle(funcName):
    global handledFuncMap, sampleNum
    print("GetSameFuncHandle funcName", funcName)
    ansList = []
    numList = []
    if (funcName in handledFuncMap):
        for i in range(5):
            lh = len(handledFuncMap[funcName][i])
            numList.append(lh)
            if (lh<=sampleNum):
                ansList.append(handledFuncMap[funcName][i])#handledFuncMap[funcName][i]: [[funcName, codes], xxx]funcName is where the EH code snippet located in, codes is the error-handling code snippet.
            else:
                ansList.append(random.sample(handledFuncMap[funcName][i], sampleNum))
    else:
        return None
    print("GetSameFuncHandle ansList", ansList)
    changedAnsList = [[], [], [], [], []]
    changedNumList = []

    for i in range(5):
        for curindex, eachFunc in enumerate(ansList[i]):
            tp = FormLearningPrompt(funcName, eachFunc[0])
            if (tp!=None):
                changedAnsList[i].append(tp)
        changedNumList.append(changedAnsList[i])
    #return ansList, numList
    return changedAnsList, changedNumList

header = []
headerSource = []
threadNameList = []
threadNameMark = []
def ThreadAnalysisInit():
    global header, headerSource, nameListForReach, threadNameMark, threadNameList
    header = []
    headerSource = []
    threadNameList = []
    threadNameMark = [0 for _ in nameListForReach]

def DirectThreadAna(namePos):
    global threadNameList
    if (namePos in callerGraph):
        threadNameList = callerGraph[namePos]
    threadNameList = []

def ThreadAnalysis(namePos):
    global callerGraph, header, headerSource, nameSet, nameListForReach, threadNameList, threadNameMark, HandledFuncDict
    curPos = len(header)
    #temptHeader = [curPos]
    temptHeader = []
    #threadNameList.append(nameListForReach[namePos])
    threadNameMark[namePos] = 1
    header.append(None)
    headerSource.append(None)
    calleeFunc = nameListForReach[namePos]
    threadNameList.append(calleeFunc)

    if (namePos in callerGraph):
        tempt = callerGraph[namePos]

        newtempt = []
        for sigt in tempt:
            callerName = nameListForReach[sigt]
            if (callerName in HandledFuncDict and calleeFunc in HandledFuncDict[callerName]):
                continue
            newtempt.append(sigt)
        tempt = newtempt

        if (len(tempt)<ThreadLengthThreshold):
            for siga in tempt:
                if (threadNameMark[siga]==0):
                    temptHeader.append(siga)
                    ThreadAnalysis(siga)
    header[curPos] = temptHeader
    headerSource[curPos] = namePos

def FixAgent(prompt):
    fixFuncList, eachAddFuc = FixPromptAnalysis(prompt)
    return fixFuncList, eachAddFuc

def FixPromptAnalysis(response):
    fixFuncList = []
    eachAddFuc = []

    return fixFuncList, eachAddFuc

def OldPEHBugPreProcess(orignalPorjectName, testProjectName, testNum):
    global funcEHCodeMap, canalyzer, handledFuncMap, callerGraph, callGraph, nameSet, nameListForReach
    print("OldPEHBugPreProcess Start")
    testThreadList = load_variable(TestDataSetDir + orignalPorjectName + "_TestData.pickle")
    bugDict = testThreadList.bugPos

    EHRepairEnvSetup(testProjectName)

    # print("canalyzer.pathDict", canalyzer.pathDict)
    counter = 0
    newBugDict = {}
    print("PEH Bug Num", len(bugDict.items()))
    #a=input()
    for bpath, bugPos in bugDict.items():
        bpath = bpath.replace(orignalPorjectName, testProjectName)
        print("bpath, bugPos", bpath, bugPos)
        newbugPos = []
        for lineIndex, tmp in enumerate(bugPos):
            if (tmp == None):
                continue
            lineNumber, blamePosFunc, funcName, ChangedFunc, ChangeItem, ChangeCodeList, funcPosList, curedges = tmp
            if (len(ChangedFunc) > 2):
                print("good example")
                print("blamePosFunc", blamePosFunc)
                print("funcName", funcName)
                print("ChangedFunc", ChangedFunc)
                print("ChangeItem", ChangeItem)
                print("ChangeCodeList", ChangeCodeList)
            #sigRepDict = None
            sigRepDict = {}

            if (sigRepDict != None):
                if (len(ChangedFunc)>2):
                    print("good example")
                    print("blamePosFunc", blamePosFunc)
                    print("funcName", funcName)
                    print("ChangedFunc", ChangedFunc)
                    print("ChangeItem", ChangeItem)
                    print("ChangeCodeList", ChangeCodeList)
                newbugPos.append([lineNumber, blamePosFunc, funcName, ChangedFunc, ChangeItem, ChangeCodeList, sigRepDict, funcPosList, curedges])
        if (newbugPos != []):
            newBugDict[bpath] = newbugPos
        counter+=1
        if (counter>testNum):
            break
    testThreadList.bugPos = newBugDict
    save_variable(testThreadList, TestDataSetDir + orignalPorjectName + "_rewrite_TestData.pickle")
    print("OldPEHBugPreProcess Done")

def FurtherReach(curFuncName, funcList, curedges, totalFList, funcMarkList):
    tP = funcList.index(curFuncName)
    #tarList = curedges[tP]
    #print("FurtherReach tarList", tarList)
    ansList = []
    nextList = curedges[tP]

    while(nextList!=[]):
        newnext = []
        for eachtar in nextList:
            #eachtar = funcList.index(eachtarFunc)
            if (funcMarkList[eachtar] == 0):
                funcMarkList[eachtar] = 1
                for eachLinkedPos in curedges[eachtar]:
                    eachtarFunc = funcList[eachLinkedPos]
                    print("FurtherReach", eachtarFunc)
                    if (eachtarFunc not in totalFList):
                        newnext.append(eachLinkedPos)
                    else:
                        ansList.append(eachtarFunc)
        nextList = newnext

    return funcMarkList, ansList

def ConstructTree(blameFunc, changedFuncList, funcList, curedges):
    global callGraph, callerGraph, nameListForReach, thirdPartyCallerGraph
    totalFList = [blameFunc]
    totalFList.extend(changedFuncList)
    print("ConstructTree", totalFList, len(nameListForReach))
    bfsList = [0]
    cNum = len(totalFList)
    markList = [0 for _ in range(cNum)]
    edgeList = [[] for _ in range(cNum)]
    stoper = 0
    markList[0] = 1
    if (blameFunc == None):
        print("No blameFunc", changedFuncList)
        bfsList = [1]
        markList[1] = 1
        stoper += 1

    funcListNum = len(funcList)
    funcMarkList = [0 for _ in range(funcListNum)]

    while(bfsList!=[]):
        newbfsList = []
        for eachnode in bfsList:
            tarFunc = totalFList[eachnode]
            print("tarFunc in bfsList", tarFunc)
            if (tarFunc in nameListForReach):
                print("in nameListForReach")
                tP = nameListForReach.index(tarFunc)
                #print("eachnode", eachnode, tarFunc)
                if (tP in callerGraph):
                    tarList = callerGraph[tP]
                    #print("tarList", tarList)
                    for i in range(cNum):
                        if (markList[i]==0):
                            nextF = totalFList[i]
                            #newbfsList.append(i)
                            #markList[i] = 1

                            if (nextF in nameListForReach and nameListForReach.index(nextF) in tarList):
                                print("Add a new next", nextF)
                                newbfsList.append(i)
                                markList[i] = 1
                                stoper += 1
                                edgeList[eachnode].append(i)
            else:#this func is not defined in this project.
                print("tarFunc in third party")
                if (tarFunc in thirdPartyCallerGraph):
                    tarList = thirdPartyCallerGraph[tarFunc]
                    #print("third party tarList", tarList)
                    for i in range(cNum):
                        if (markList[i] == 0):
                            nextF = totalFList[i]
                            #newbfsList.append(i)
                            #markList[i] = 1
                            if (nextF in tarList):
                                print("Add a new next in else", nextF)
                                newbfsList.append(i)
                                markList[i] = 1
                                stoper += 1
                                edgeList[eachnode].append(i)
                else:
                    print("Error: Func Name not exist")

            if (tarFunc in funcList):
                print("in funcList")
                funcMarkList, ansList = FurtherReach(tarFunc, funcList, curedges, totalFList, funcMarkList)
                for eacha in ansList:
                    totoalPos = totalFList.index(eacha)
                    if (markList[totoalPos] == 0):
                        print("Add a new next", eacha)
                        newbfsList.append(totoalPos)
                        markList[totoalPos] = 1
                        stoper += 1
                        edgeList[eachnode].append(totoalPos)
                '''tP = funcList.index(tarFunc)
                tarList = curedges[tP]
                for eachtar in tarList:
                    if (funcMarkList[eachtar] == 0):#visit mark for funcList
                        funcMarkList[eachtar] = 1
                        eachtarFunc = funcList[eachtar]
                        if (eachtarFunc in totalFList):#link an edge from tarFunc to eachtarFunc
                            totoalPos = totalFList.index(eachtarFunc)
                            if (markList[totoalPos]==0):
                                newbfsList.append(totoalPos)
                                markList[totoalPos] = 1
                                edgeList[eachnode].append(totoalPos)'''

        bfsList = newbfsList
        if (stoper == cNum):#all func are visited
            break
        print("newbfsList is:", bfsList)

    #show the tree

    if (stoper != cNum):
        print("Some functions are not been found")

    for i in range(cNum):
        outAns = ""
        for j in edgeList[i]:
            outAns += totalFList[j] + " "
        if (outAns!=""):
            print("Func", totalFList[i])
            print("Called:", outAns)

def propagationPathOutPut(blameFunc, funcList, edges):
    global thirdPartyCallerGraph
    outputInfo = ""
    cnum = len(funcList)
    if (blameFunc not in funcList and blameFunc in thirdPartyCallerGraph):
        tempList = thirdPartyCallerGraph[blameFunc]
        print("Blame Func:", blameFunc)
        outputInfo += "Blame Func:" + blameFunc + "\n"
        ans = ""
        for i in range(cnum):
            if (funcList[i] in tempList):
                ans += " " + funcList[i]
        print("Caller:", ans)
        outputInfo += "Caller:" + ans + "\n"

    if (cnum!=len(edges)):
        print("propagationPathOutPut Not correct")
        print("funcList", len(funcList), funcList)
        print("edges", len(edges), edges)
        outputInfo = None
        return outputInfo
    print("propagationPath")
    outputInfo += "propagationPath\n"
    for i in range(cnum):
        ans = ""
        for j in edges[i]:
            ans+=" " + funcList[j]
        if (ans!=""):
            print("Func:", funcList[i])
            print("Caller:", ans)
            outputInfo += "Func: " + funcList[i] + "\nCaller: " + ans + "\n"
    print("propagationPath End")
    outputInfo += "propagationPath End\n"
    return outputInfo

def EHFix(testProjectName, bpath, bugPos):
    global funcEHCodeMap, canalyzer, handledFuncMap, callerGraph, callGraph, nameSet, nameListForReach
    global rewriteDict, reRewriteDict
    print("EHBugTestSet Start")
    #clearTestData("curTestData.txt")
    #print(bugDict)
    # GroundTruthDict = testThreadList.groundTruth
    #changeList = testThreadList.changeList
    rewriteDict = {}
    EHRepairEnvSetup(testProjectName)
    temptTestResult = open("GPT-testResult.txt", "w")
    writeCounter = 0
    testDataList = []
    #pos, posFuncName, ChangedFunc, ChangeItem = bugPos
    #curGroundTruth = GroundTruthDict[bpath]
    #bpath = bpath.replace(orignalPorjectName, testProjectName)
    #print("lineNumber", bpath, bugPos)
    for lineIndex, tmp in enumerate(bugPos):
        lineNumber, blameFunc, funcName, ChangedFunc, ChangeItem, ChangeCodeList, sigRepDict, funcList, curedges = tmp

        #print("bug starter", funcName, lineNumber)
        #print("GroundTruth ChangedFunc", ChangedFunc)
        #print("GroundTruth ChangeItem", ChangeItem)
        if (ChangedFunc[0] == "swiotlb_memblock_alloc"):
            continue
        temptChangedFunc = listRewrite(ChangedFunc)
        temptChangeItem = groupRewrite(ChangeItem)
        tarLen = len(temptChangedFunc)
        tarItemLen = len(temptChangeItem)
        tarCLen = len(ChangeCodeList)
        outputInfo = ""

        if (tarLen > 5):
            continue

        outputInfo += "\n\n---\nChanged Func Num: " + str(tarLen) + "\n"
        outputInfo += "blameFunc: " + blameFunc + "\n"
        outputInfo += "---temptChangedFunc---" + " " + str(len(temptChangedFunc)) + "\n" + " ".join(temptChangedFunc) + "\n" + "---temptChangedFunc End---\n"
        #print("Length", tarLen, tarItemLen, tarCLen)
        #print("blameFunc", blameFunc)
        #print("temptChangedFunc", len(temptChangedFunc), temptChangedFunc)
        #print("temptChangeItem", temptChangeItem)
        #print("Start from", funcName)
        outputInfo += f"Start from {funcName}\n"
        oc = propagationPathOutPut(blameFunc, funcList, curedges)
        if (oc == None):
            continue
        #ConstructTree(blameFunc, ChangedFunc, funcList, curedges)
        outputInfo += "\n\n---Call Graph---\n" + oc + "---Call Graph End---\n\n"

        skipFlag = False

        for sigli in range(tarLen):
            outputInfo += "---Single Detail---\n ChangedFunc\n" + temptChangedFunc[sigli] + "\n"
            outputInfo += "ChangeItem\n" + " ".join(temptChangeItem[sigli]) + "\n"
            outputInfo += "---ChangeCodeList Before---\n" + ChangeCodeList[sigli][0].replace("\\n", "\n") + "\n---ChangeCodeList Before End---\n"
            outputInfo += "---ChangedFunc---\n" + ChangeCodeList[sigli][1].replace("\\n", "\n") + "---ChangedFunc End---\n---Single Detail End---\n\n"
            #print("GroundTruth ChangedFunc", temptChangedFunc[sigli])
            #print("GroundTruth ChangeItem", temptChangeItem[sigli])
            #print("GroundTruth ChangeCodeList Before\n", ChangeCodeList[sigli][0].replace("\\n", "\n"))
            #print("GroundTruth ChangeCodeList After\n", ChangeCodeList[sigli][1].replace("\\n", "\n"))
            if (len(temptChangeItem[sigli])>3 and "---------GOTO----------" not in ChangeCodeList[sigli][0]):
                skipFlag = True
                break

        if (skipFlag):
            continue

        releventInfo = EHBugRepair(bpath, lineNumber, funcName)
        if (releventInfo!=None):
            newErrFunc, newInFuncName, oriCode, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes = releventInfo
            outputInfo += "\n\n---RAG Info---\n\n"
            outputInfo += "\n\n---relatedCodeList---\n\n" + "\n".join(relatedCodeList) + "\n\n---relatedCodeList End---\n\n"

            outputInfo += "\n\n---sameFileCodes---\n\n"
            for round, eachStrategy in enumerate(sameFileCodes):
                outputInfo += f"\nstrategy: {round}\n"
                outputInfo += "\n".join(eachStrategy)
            outputInfo += "\n\n---sameFileCodes End---\n\n"

            outputInfo += "\n\n---sameFuncHandleCodes---\n\n"
            for round, eachStrategy in enumerate(sameFuncHandleCodes):
                outputInfo += f"\nstrategy: {round}\n"
                outputInfo += "\n".join(eachStrategy)
            outputInfo += "\n\n---sameFuncHandleCodes End---\n\n"

            outputInfo += "\n\n---RAG Info End---\n\n"
        else:
            continue

        temptTestResult.write(outputInfo)

        #print("sigRepDict", sigRepDict)
        rewriteDict = sigRepDict
        reRewriteDict = {value: key for key, value in rewriteDict.items()}
        #c = input("hold")
        #if (c == " "):
        #    continue

        '''
        result = EHBugRepair(bpath, lineNumber, funcName)#修复bug
        if result!=None:
            changedFuncList, actionsList, patchList, deepList = result
            print("GroundTruth ChangedFunc", ChangedFunc)
            print("GroundTruth ChangeItem", ChangeItem)
            print("Fix Result changedFuncList", changedFuncList)
            print("Fix Result actionsList", actionsList)
            print("Fix Result patchList", patchList)
            print("Fix Result deepList", deepList)
        else:
            print("Fix Fail")
        '''

        #stop = input()
        '''if (otData!=None):
            otData.append(ChangedFunc)
            otData.append(ChangeItem)
            testDataList.append(otData)
            writeCounter += 1
            #Write2File(otData, ChangedFunc, ChangeItem, "curTestData.txt")
        else:
            print("EHBugTestSet Skip")'''
    #print("writeCounter", writeCounter)
    #save_variable(testDataList, f"{testProjectName}_testDataList.pickle")

def EHRepairEnvSetup(projectName):
    global handledFuncMap, callerGraph, callGraph, nameSet, nameListForReach, funcCodeDict, ErrorCodeMap, thirdPartyCallerGraph
    global returnBackGroundPrompt, HandledFuncDict, funcHandledMap, Type2CleanUp
    LoadCode2PathFromFile(projectName)
    loadSavedAnaSet(projectName)
    handledFuncMap = load_variable(RetDataSetDir + projectName + "_handledFuncMap.pickle")
    HandledFuncDict = load_variable(RetDataSetDir + projectName + "_HandledFuncDict.pickle")
    #print("HandledFuncDict", HandledFuncDict)
    ErrorCodeMap = load_variable(RetDataSetDir + projectName + "_ErrorCodeMap.pickle")
    Type2CleanUp = load_variable(RetDataSetDir + projectName + "_Type2CleanUp.pickle")
    funcHandledMap = load_variable(RetDataSetDir + projectName + "_funcHandledMap.pickle")

    filter_functions_by_frequency(1)
    #print("returnBackGroundPrompt", returnBackGroundPrompt)
    #print("EHRepairEnvSetup handledFuncMap", handledFuncMap)
    #print("Map Loaded")
    print("EHRepairEnvSetup", projectName)
    varDict = load_variables(projectName)
    # funcDefSumDict = varDict["funcDefSumDict"]
    # funcBackGround = varDict["funcBackGround"]
    nameListForReach = varDict["nameListForReach"]
    funcCodeDict = varDict["funcCodeDict"]
    #print('funcCodeDict fmt_single_name', funcCodeDict["fmt_single_name"])
    nameSet = set(nameListForReach)
    print("Var Loaded")
    # resRepGlobList = varDict["resRepGlobList"]
    # funcSuspiciousDict = varDict["funcSuspiciousDict"]
    # funcDefOrder = varDict["funcDefOrder"]
    # funcSuspiciousAccessDict = {}
    # funcSuspiciousCallPathDict = {}
    # funcTypeDict = varDict["funcTypeDict"]
    # globalContext = varDict["globalContext"]
    # funcReturnFuncList = varDict["funcReturnFuncList"]
    callerGraph = varDict["callerGraph"]
    callGraph = varDict["callGraph"]
    thirdPartyCallerGraph = varDict["thirdPartyCallerGraph"]
    # print("callerGraph", callerGraph)
    # print("callGraph", callGraph)
    # print("nameListForReach", nameListForReach)

def CallGraphPrompt():
    global threadNameList, nameListForReach, header, headerSource
    callDict = {}
    ans = "\n"
    hlen = len(headerSource)
    for i in range(hlen):
        if (header[i]!=[]):
            calleeName = nameListForReach[headerSource[i]]
            ans += calleeName + " is called by :"
            callDict[calleeName] = []
            for sigh in header[i]:
                callerName = nameListForReach[sigh]
                callDict[calleeName].append(callerName)
                ans += " " + callerName
            ans += "\n"
    return ans, callDict

def filter_top_m_errors(m, t):
    global ErrorCodeMap

    filtered_for_minimum = {error_code: snippets for error_code, snippets in ErrorCodeMap.items() if len(snippets) >= t}

    sorted_errors = sorted(filtered_for_minimum.items(), key=lambda item: len(item[1]), reverse=True)[:m]

    ErrorCodeMap = {error_code: snippets for error_code, snippets in sorted_errors}

def filter_functions_by_frequency(freqTS):
    global Type2CleanUp
    #print("filter_functions_by_frequency before", Type2CleanUp)

    filtered_dict = {}

    for datatype, functions in Type2CleanUp.items():

        func_counter = Counter(functions)


        filtered_functions = [func for func, count in func_counter.items() if count >= freqTS]


        if filtered_functions:
            filtered_dict[datatype] = filtered_functions

    Type2CleanUp = filtered_dict
    #print("filter_functions_by_frequency after", Type2CleanUp)

def ReturnBackGroundPrompt(n):
    global ErrorCodeMap, returnBackGroundPrompt
    #print("ErrorCodeMap", ErrorCodeMap)
    filter_top_m_errors(30, 1)
    for error_code, snippets in ErrorCodeMap.items():
        returnBackGroundPrompt += f"Error Code: {error_code}\n"
        examples_to_show = snippets[:n]

        for snippet in examples_to_show:
            returnBackGroundPrompt += f"- {snippet}\n"

        returnBackGroundPrompt += "\n"

def PropagationCodeList():
    global funcCodeDict, threadNameList
    ansList = []
    relatedFuncDict = {}
    ans = "\n"
    for signame in threadNameList:
        if signame in funcCodeDict:
            ans += f"Source code of {signame}: "
            ans += funcCodeDict[signame]
            ansList.append(funcCodeDict[signame])
            relatedFuncDict[signame] = funcCodeDict[signame]
            ans += "\n\n"
    return ans, ansList, relatedFuncDict

def clearTestData(path):
    open(path, "w").close()

def Write2File(dataList, ChangedFunc, ChangeItem, path):
    with open(path, "a") as file:
        inFuncName, errFunc, errCount, errCodes, bpath, lineNumber, ContextPrompt, SameFileCodePrompt, OtherHandlingPrompt, propaCode, sameFileCodesPrompt, sameFuncHandleCodesPrompt = dataList
        print("-----------------------------Start----------------------------------\n", file=file)
        print(f"inFuncName: {bpath}, {inFuncName}, {errFunc} miss EH\n", file=file)
        print(f"errCount: {errCount}, {errCodes} miss EH\n", file=file)
        print(f"ChangedFunc: {ChangedFunc}, ChangeItem: {ChangeItem}\n", file=file)
        print(ContextPrompt+"\n", file=file)
        print(SameFileCodePrompt + "\n", file=file)
        print(OtherHandlingPrompt + "\n", file=file)
        print("-----------------------------End----------------------------------\n", file=file)

def FormFixingPrompt(blameFunc, buggyFunc, buggySource, someFuncHandleSum, sameFileHandleSum):
    basePrompt = f"The {blameFunc} in {buggyFunc} lacks proper error handling. Assume the role of an experienced software engineer.\
    You should proceed according to the following steps:\n\
1、Summarize the impact of the error.\n\
Describe the occurrence and impact of the error on the {buggySource}.\n\
Describe how buggy function impact its callers in case of error.\n\
This analysis should detail how each error affects the operation.\n\
2、Predict how the error should be handled.\n\
Whether error handling is necessary;\n\
Whether logging is required;\n\
Which resources need to be released;\n\
What error codes should be returned;\n\
Here are some examples to help you understand the error handling style of the current software:\n"
    sFuncHPrompt = ""
    if (someFuncHandleSum!=[]):
        for eachItem in someFuncHandleSum:
            sFuncHPrompt += f"Here are some examples how {blameFunc} is handled in other functions:\n{eachItem}\n"
    sFileHPrompt = ""
    if (sameFileHandleSum!=[]):
        for eachItem in sameFileHandleSum:
            sFileHPrompt += f"Here are some examples how functions in the same module as {buggyFunc} is handling errors:\n{eachItem}\n"

    endPrompt = f"Respond with specific tags as outlined below:\n\
[STEP1_Summary]A brief summary within 100 tokens explaining how error occurred, how it affects the buggy function, \
how buggy function could affect its callers.[/STEP2_Summary]\n\
If {blameFunc} don’t need to be handled, don’t output the rest result.\n\
[STEP2_Handling_Strategy] How {blameFunc} should be handled considering the handling style of the current software. [/STEP2_Handling_Strategy]"
    return basePrompt + sFuncHPrompt + sFileHPrompt + endPrompt

def FormLearningPrompt(blameFunc, buggyFunc):#FormLearningPrompt
    global nameSet, nameListForReach, funcEHCodeMap, funcCodeDict, callerGraph
    print("GenerateTestPrompt", blameFunc, buggyFunc)
    if (blameFunc == None or buggyFunc == None):
        return None
    callList = None
    if (buggyFunc in nameSet):
        bfPos = nameListForReach.index(buggyFunc)
        if (bfPos in callerGraph):
            callList = callerGraph[bfPos]
    blameFuncSource = None
    if (blameFunc in funcCodeDict):
        blameFuncSource = funcCodeDict[blameFunc]
    buggyFuncSource = None
    print("funcCodeDict len", len(funcCodeDict.keys()))
    if (buggyFunc in funcCodeDict):
        buggyFuncSource = funcCodeDict[buggyFunc]
    else:
        return None#this is not acceptable
    print("Here")
    ListOfSource = []
    if (callList!=None):
        for eachIndex in callList:
            curFunc = nameListForReach[eachIndex]
            if (curFunc in funcCodeDict):
                ListOfSource.append(funcCodeDict[curFunc])
    startPrompt = f"Learning handling strategies from the error-handling for {blameFunc} in {buggyFunc}. Assume the role of an experienced software engineer. You should proceed according to the following steps:\n\
\n\
Objective:\n\
Learn and analyze the error-handling strategies used within the software. These information will be used as context\n\
information to help LLM fix error-handling bug.\n\
You should proceed according to the following steps:\n\
\n\
1.Analyze error handling of {blameFunc} in the {buggyFunc}, and summarize in a natural language narrative:\n\
- Which actions (logging/cleanup/return statement) are used.\n\
- Which resources are cleaned up by which function.\n\
- Which error code is returned.\n\
If an action is not utilized, it should not be mentioned.\n\
\n\
2. Summarize the error's severity:\n\
- Describe the occurrence and impact of the error of {blameFunc} on the {buggyFunc}.\n\
- Describe how errors of {blameFunc}, if not handled in {buggyFunc}, impact callers of {buggyFunc}. This usually relate to the need for returning an error code.\
This analysis should detail how error affects the system's operations.\n\
Examples of the summarized impacts:\n\
'Impact: Configuration file fails to load, affecting system initialization.'\n\
'Impact: Configuration error leads to inaccurate data processing in its callers.'\n\
\n\
3. Correlate these impacts with targeted handling strategies, forming concise relationship pairs. For each impact, specify a precise handling action.\n\
Examples of relationship pairs:\n\
'Impact: Configuration file fails to load in buggy function, Handling Strategy: Return 'E_LOAD_FAIL'.'\n\
'Impact: Inaccurate data processing in caller, Handling Strategy: Return 'E_DATA_ERROR' for data integrity issues.'\n"
    blamePrompt = f"Source of {blameFunc} is unknown\n\n"
    if (blameFuncSource != None):
        blamePrompt = f"Source of {blameFunc} is as follow:\n {blameFuncSource}\n\n"
    buggyPrompt = f"Source of {buggyFunc} is as follow:\n {buggyFuncSource}\n\n"
    callerListPrompt = f"{buggyFunc} is not called by other functions.\n"
    if (ListOfSource != []):
        callerListPrompt = f"Source of Caller functions of {buggyFunc}:\n"
        for eachs in ListOfSource:
            callerListPrompt += f"{eachs}\n\n"
    endPrompt = f"Respond with specific tags as outlined below:\n \
If the error of {blameFunc} in {buggyFunc} is not being checked. Don't output the rest result. Note that, \"return;\", can be considered as return NULL\n\
[STEP1_Summary]A brief summary within 50 tokens explaining in the handling of {blameFunc} in {buggyFunc}, what actions were used, what resources are cleaned up, and what error code is returned.[/STEP1_Summary]\n\
[STEP2_Summary]A brief summary within 100 tokens explaining how error in {blameFunc} occurred, how it affects the {buggyFunc}, how {buggyFunc} could affect its callers.[/STEP2_Summary]\n\
[STEP3_Relation_Pair]relation pair in the form of:\
error impact -> handling action(avoid include specific function names)[/STEP3_Relation_Pair]"
    return startPrompt + blamePrompt + buggyPrompt + callerListPrompt + endPrompt

def RelatedInfoRetrive(inFuncName, errFunc):#nextFuncList = callDict[inFuncName]
    global canalyzer, funcCodeDict, rewriteDict, callerGraph, funcHandledMap
    nextFuncList = []
    handledFuncList = None
    #print('funcHandledMap', funcHandledMap.keys())
    '''if inFuncName in funcHandledMap:
        handledFuncList = funcHandledMap[inFuncName]
        print("inFuncName handledFuncList", inFuncName, ":", handledFuncList )'''
    oriCode = None
    if (inFuncName in nameSet and inFuncName in funcCodeDict):
        oriCode = funcCodeDict[inFuncName]
        #oriCode = oriCode.replace("\\n", "\n")
        oriCode = re.sub(r'(\t)(\t+)', r'\n\2', oriCode)
        #oriCode = repr(oriCode)
        #print("oriCode", oriCode)
        namePos = nameListForReach.index(inFuncName)
        if (namePos in callerGraph):
            tarList = callerGraph[namePos]

            for tarPos in tarList:
                tarname = nameListForReach[tarPos]
                if (tarname in funcHandledMap):
                    print("inFuncName tarname", inFuncName, tarname)
                    print("tarname funcHandledMap", funcHandledMap[tarname])
                    if (inFuncName in funcHandledMap[tarname]):
                        continue
                nextFuncList.append(tarname)
            #print("nextFuncList", nextFuncList)
        print("SigFuncFix", inFuncName, errFunc)
        print("oriCode", oriCode)
        print("nextFuncList", nextFuncList)
    else:
        return None

    relatedCodeList = [oriCode]
    newNextFunc = []
    for sigf in nextFuncList:
        if (sigf in funcCodeDict):
            relatedCodeList.append(re.sub(r'(\t)(\t+)', r'\n\2', funcCodeDict[sigf]))
            newNextFunc.append(sigf)

    #print("canalyzer.func2path", canalyzer.func2path.keys())
    if (inFuncName in canalyzer.func2path):
        sameFileCodes, numberList = canalyzer.get_rel_EH(canalyzer.func2path[inFuncName])
        if (sameFileCodes!=[[], [], [], [], []]):
            print("sameFileCodes", sameFileCodes)
        #sameFileCodesPrompt = generate_prompt_for_error_handling(sameFileCodes)
        sameFuncHandleCodes = [[],[],[],[],[]]
        sfhNumList = [0, 0, 0, 0, 0]
        GetSameFuncHandleAns = GetSameFuncHandle(errFunc)
        if (GetSameFuncHandleAns!=None):
            sameFuncHandleCodes, sfhNumList = GetSameFuncHandleAns
            if (sameFuncHandleCodes!=[[], [], [], [], []]):
                print("Here is a success search sameFuncHandleCodes", sameFuncHandleCodes)
        #sameFuncHandleCodesPrompt = generate_prompt_for_error_handling(sameFuncHandleCodes)
        if (rewriteDict!=None):#Is testing Old PEH bug, need replacement
            initalRepDict(rewriteDict)
            #print("errFunc before", errFunc)
            errFunc = strRewrite(errFunc)
            #print("errFunc after", errFunc)
            #print("inFuncName before", inFuncName)
            inFuncName = strRewrite(inFuncName)
            #print("inFuncName after", inFuncName)
            #print("oriCode before", oriCode)
            oriCode = strRewrite(oriCode)
            #print("oriCode after", oriCode)
            #print("newNextFunc before", newNextFunc)
            newNextFunc = listRewrite(newNextFunc)
            #print("newNextFunc after", newNextFunc)
            #print("relatedCodeList before", relatedCodeList)
            relatedCodeList = listRewrite(relatedCodeList)
            #print("relatedCodeList after", relatedCodeList)
            #print("sameFileCodes before", sameFileCodes)
            sameFileCodes = groupRewrite(sameFileCodes)
            #print("sameFileCodes after", sameFileCodes)
            #print("sameFuncHandleCodes before", sameFuncHandleCodes)
            #sameFuncHandleCodes = groupRewrite(sameFuncHandleCodes)
            #print("sameFuncHandleCodes after", sameFuncHandleCodes)
        #wait = input("")
        errFunc = clust(errFunc)
        ans = FixAg(errFunc, inFuncName, oriCode, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes, 0)
        print("FixAg ans", ans)
        return ans
    else:
        print("Not here")
        return None

def obListCollect(bpath, lineNumber):

    tmp = canalyzer.find_function_name(bpath, lineNumber)
    if tmp == None:
        print("Tmp == None")
        return None
    inFuncName, _, _, _, _ = tmp
    ThreadAnalysisInit()
    if (inFuncName in nameSet):
        namePos = nameListForReach.index(inFuncName)
        ThreadAnalysis(namePos)
        propaCode, _, _ = PropagationCodeList()
        return formRepDict(propaCode)
    else:
        return None

ehBugRepairLog = []

def EHBugRepair(bpath, lineNumber, funcName):
    global funcEHCodeMap, canalyzer, handledFuncMap, callerGraph, callGraph, nameSet
    global nameListForReach, ErrorCodeMap
    global returnBackGroundPrompt, funcCodeDict
    global overAllStopIterate, provSet
    global ehBugRepairLog
    overAllStopIterate = 30#Prevent too much fix
    tmp = canalyzer.find_function_name(bpath, lineNumber)
    if tmp == None:
        print("Tmp == None")
        return None
    inFuncName, errFunc, errLine, errCount, errCodes = tmp
    print("EHBugRepair", inFuncName, errFunc, errCount)
    print("EHBugRepair errCodes", errCodes)
    tempt = RelatedInfoRetrive(inFuncName, errFunc)
    newErrFunc, newInFuncName, oriCode, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes = tempt
    provSet = set()
    ehBugRepairLog = []
    return FixAg(newErrFunc, newInFuncName, oriCode, errLine, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes, None, 0)

def funcCheckPrepare(c_code):
    global provSet
    curset = nameExtract(c_code)
    #print("provSet", provSet)
    #print("curset", curset)
    if (curset.issubset(provSet)):
        return None
    else:
        ans = curset - provSet
        #print("funcCheckPrepare", ans)
        return ans

def providedSet(initalInput):
    global provSet
    provSet = provSet.union(nameExtract(initalInput))

def nameExtract(oriCode):
    # 移除单行和多行注释
    clean_code = re.sub(r'//.*?$', '', oriCode, flags=re.MULTILINE)
    clean_code = re.sub(r'/\*.*?\*/', '', clean_code, flags=re.DOTALL)

    clean_code = re.sub(r'"(\\.|[^"\\])*"', '', clean_code)

    clean_code = re.sub(r'\b\d+(\.\d+)?\b', '', clean_code)

    pattern = r'\b(\w+)\b'

    matches = re.finditer(pattern, clean_code)

    c_keywords_types = set([
        "int", "float", "char", "double", "long", "short", "unsigned", "signed",
        "void", "return", "if", "else", "while", "for", "sizeof", "struct",
        "typedef", "static", "enum", "const"
    ])


    identifiers = set()

    for match in matches:
        identifier = match.group(1)
        if identifier not in c_keywords_types:
            identifiers.add(identifier)


    return identifiers

def CodeIRRetrive(codeIRList):
    global funcCodeDict, reRewriteDict
    counter = 0
    ans = ""
    for sigName in codeIRList:
        if (reRewriteDict!=None and sigName in reRewriteDict):
            sigName = reRewriteDict[sigName]
        if (sigName in funcCodeDict):
            tp = funcCodeDict[sigName]
            ans += tp + "\n"
            counter += 1
    if (counter == len(codeIRList)):
        return True, ans
    else:
        return False, ans


def Cleanup_Function(typeIRList):
    global Type2CleanUp, reRewriteDict
    counter = 0
    ans = ""
    for sigName in typeIRList:
        nList = sigName.split(" ")
        sigName = nList[0]
        if (sigName == 'struct'):
            sigName = nList[1]

        while (sigName[-1] == '*'):
            sigName = sigName[:-1]

        print("Cleanup_Function sigType", sigName)
        if (reRewriteDict!=None and sigName in reRewriteDict):
            sigName = reRewriteDict[sigName]
            print("Cleanup_Function rewrite sigType", sigName)
        if (sigName in Type2CleanUp):
            tp = Type2CleanUp[sigName]
            ans += tp + "\n"
            counter += 1
    if (counter == len(typeIRList)):
        return True, ans
    else:
        return False, ans

def IRRetrive(IRRequest):
    global funcCodeDict, Type2CleanUp
    irList = IRRequest.split("\n")
    ans = ""
    for sigir in irList:
        detIR = sigir.split(" ")
        if (len(detIR)!=2):
            continue
        irinfo, targetName = detIR
        if ("Source_Code" in irinfo):
            if(targetName in funcCodeDict):
                tp = funcCodeDict[targetName]
                ans += tp + "\n"
        elif ("Cleanup_Function" in irinfo):
            if (targetName in Type2CleanUp):
                tp = Type2CleanUp[targetName]
                ans += tp + "\n"
    if (ans == ""):
        return None
    return ans

def findErrLine(calleeFunc, sourceCode):
    lines = sourceCode.split("\n")
    for sigLine in lines:
        match = re.search(r'\b{}\s*\('.format(calleeFunc), sigLine)
        if (match):
            return sigLine
    return None


def funcNameRepalce(funcName):
    global reRewriteDict
    if (reRewriteDict!=None and funcName in reRewriteDict):
        return reRewriteDict[funcName]
    return funcName


def FixAg(errFunc, inFunc, oriCode, errLine, callerList, relatedCodeList, sameFileCodes, sameFuncHandleCodes, lastPatch, deepth):
    global provSet, overAllStopIterate, ehBugRepairLog
    ehBugRepairLog.append(inFunc)#Log this functions
    overAllStopIterate -= 1
    if(overAllStopIterate <=0):
        print("overAllStopIterate Expired")
        return None
    print("FixAg Start")
    # The return value
    changedFuncList = []
    handlingAList = []
    patchList = []
    deepList = []
    callDes = ", ".join(callerList)
    contextCode = "\n".join(relatedCodeList)
    SameFileCode = generate_prompt_for_error_handling(sameFileCodes)
    OtherEH = generate_prompt_for_error_handling(sameFuncHandleCodes)

    startPrompt = f"The {errFunc} in {inFunc} is missing error handling.\n The buggy line is {errLine}.\n"
    if (lastPatch!=None):
        startPrompt = f"An error handling bug was fixed in {errFunc} and return an error code. This return value could \
cause an error handling bug in {inFunc}. The fix in {errFunc} is as follow: {lastPatch}\n. If {errFunc} did cause an error-handling bug in {inFunc}, help me fix it.\n"

    basicPrompt = startPrompt + f"Note that:\n\
1.Concentrate on the error generated by {errFunc} in {inFunc} only, \
and chose the most suitable handling by considering its severity and context.\n\
2.Use only functions and error codes in the following code.\n\
3.The 'Code' should only contain codes to replace the buggy code, nothing else.\n\
4.Output in one json mentioned in the example without analysis.\n"
    callGraphDescribe = f"{inFunc} is called by:\n {callDes}\nFunctions in 'Need_Fix' should be selected from these caller.\n"

    relatedPrompt = f"Here is the source code of the {inFunc} and its caller functions ({callDes}):\n {contextCode}"
    if (len(callerList) == 0):
        callGraphDescribe = f"{inFunc} is not called by other functions, so no functions will be selected into 'Need_Fix'\n"
        relatedPrompt = f"Here is the source code of the {inFunc}:\n {contextCode}"
    OtherHandlingPrompt = ""
    if (OtherEH == ""):
        OtherHandlingPrompt = f"The following is the error handling for the {errFunc} in another location:\n{OtherEH}"
    SameFileCodePrompt = ""
    if (SameFileCode == ""):
        SameFileCodePrompt = f"The following are other error handling in the same module:\n{SameFileCode}"

    patchGenPrompt = basicPrompt + callGraphDescribe + relatedPrompt + OtherHandlingPrompt + SameFileCodePrompt
    providedSet(patchGenPrompt)

    IterateTime = 3
    historicalPrompt = oneshotPrompt()#
    genFlag = False
    newlist = []
    backTrack = False
    while (IterateTime):
        IterateTime -= 1
        temp = PatchGenerate(patchGenPrompt, historicalPrompt)

        if (temp == None):
            patchGenPrompt = None
            continue
        flag, gptReturnText, patch, newlist = temp
        if (patch == None or newlist == None):
            patchGenPrompt = None
            continue

        print(f"Got a patch---------------------------\n{patch}\nPatchFinish---------------------------\nnewlist: {newlist}\nnNextFunc End-----------\n")
        if (patch == None):
            patchGenPrompt = None
            continue

        if (backTrack):
            historicalPrompt = historicalPrompt[:-2]
            backTrack = False

        if (flag == 2):
            print("PATCH: More Info Required", patch)
            Need_Code_Lists, Need_Clean_Method_Lists = patch
            if (Need_Code_Lists == None and Need_Clean_Method_Lists == None):
                patchGenPrompt = None  # The IR request is in wrong format
                continue

            findAllCodeFlag, needCodeP = CodeIRRetrive(Need_Code_Lists)
            print("needCodeP", needCodeP)
            findAllCleanFlag, cleanMethodP = Cleanup_Function(Need_Clean_Method_Lists)
            print("cleanMethodP", cleanMethodP)
            if (needCodeP == "" and len(Need_Code_Lists)>0):
                needCodeP = "The source code you request is not found.\n"
            elif (findAllCodeFlag == False):
                needCodeP += "The rest source code you request is not found.\n"
            if (cleanMethodP == "" and len(Need_Clean_Method_Lists)>0):
                cleanMethodP = "The cleanup method of the datatype you request is not found, if they cannot be handled \
using functions from glibc, they never been cleaned in this software.\n"
            elif (findAllCleanFlag == False):
                cleanMethodP += "The cleanup method of the rest datatype you request is not found, if they cannot be handled \
using functions from glibc, they never been cleaned in this software.\n"
            patchGenPrompt = needCodeP + cleanMethodP
            patchGenPrompt += "\nPlease try to fix the buggy line and output in json format."
            backTrack = True
            patchGenPrompt = strRewrite(patchGenPrompt)
            moreName = nameExtract(patchGenPrompt)
            provSet = provSet.union(moreName)
            lastInfo = [{
                "role": "GPT",
                "content": gptReturnText,
            }]
            historicalPrompt.extend(lastInfo)
            continue
        else:
            if (patch == "_PASS_"):
                print("PATCH: Pass")
                genFlag = True
                changedFuncList.append(inFunc)
                handlingAList.append([])
                patchList.append("Pass")
                deepList.append(deepth)
                break
            formatError = funcCheckPrepare(patch)
            if (formatError!=None):
                print("PATCH: Patch format Error")
                patchGenPrompt = f"The {formatError} is not from the input, please regenerate and use only functions and error codes in the provided codes"
                print("funcCheckPrepare failed:", patchGenPrompt)
                lastInfo = [{
                    "role": "GPT",
                    "content": gptReturnText,
                }]
                backTrack = True
                # patchMessageAdd(lastInfo)
                historicalPrompt.extend(lastInfo)
                continue
            tempt = None
            tryTime = 3
            while(tempt == None and tryTime>0):
                tryTime -= 1
                tempt = CheckAgent(patch, oriCode, errLine, errFunc, inFunc)
            if (tempt == None):
                print("Check Agent Error")
                return None  # Fix failed
            ans, handlingActions, fixedCode, wrongMessage = tempt
            print("Check Result", ans, wrongMessage)
            if (ans):
                genFlag = True
                print("passed Ans", inFunc, deepth, patch)
                print("handlingActions", handlingActions)
                print("fixedCode----------\n", fixedCode, "fixedCodeEnd----------")
                changedFuncList.append(inFunc)
                patchList.append(patch)
                handlingAList.append(handlingActions)
                deepList.append(deepth)
                lastPatch = patch
                print("changedFuncList", changedFuncList)
                print("patchList", patchList)
                print("deepList", deepList)
                break
            lastInfo = [{
                "role": "GPT",
                "content": gptReturnText,
            }]
            historicalPrompt.extend(lastInfo)
            patchGenPrompt = f"The current patch is incorrect and the main issues are as follows:{wrongMessage}\n. Please regenerate the patch\n"
            backTrack = True
            continue
    if (genFlag):
        print("Next Stage", newlist)
        searchInFunc = funcNameRepalce(inFunc)

        temptNewList = []
        for sign in newlist:
            if sign not in ehBugRepairLog:
                temptNewList.append(sign)
        newlist = temptNewList


        for sign in newlist:
            print("retrive info", sign, inFunc)
            sign = funcNameRepalce(sign)
            inFunc = funcNameRepalce(inFunc)
            print("After rewrite back", sign, inFunc)
            tempt = RelatedInfoRetrive(sign, inFunc)
            if (tempt == None):
                return None
            newInFunc, newsign, oriCode, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes = tempt
            print("newNextFunc", newNextFunc)
            newErrLine = findErrLine(inFunc, oriCode)
            fixans = FixAg(newInFunc, newsign, oriCode, newErrLine, newNextFunc, relatedCodeList, sameFileCodes, sameFuncHandleCodes, lastPatch, deepth+1)
            if (fixans == None):
                return None
            lastcfList, lasthaList, lastpList, lastDList = fixans
            changedFuncList.extend(lastcfList)
            handlingAList.extend(lasthaList)
            patchList.extend(patchList)
            deepList.extend(lastDList)
        return changedFuncList, handlingAList, patchList, deepList
    else:
        return None#Fix failed

def Analysis(projectName):
    load_AllEHThread_from_file(RetDataSetDir+projectName+"_AllEHThread.pickle")
    filter_and_transform_ehthreadlist(projectName)


def sigFuncVerif(projectName, timeInfo, threadInfo):
    global projectBasicPath

    commitID, origTime, formatTime = timeInfo
    path, checkPos, funcPos, blamePos, blameFunc, blameLine, branchCode, funcName, funcType, endPos, funcCode, _, fList = threadInfo

    rpath = projectBasicPath + projectName + '/'
    #print("rpath", rpath)
    #print("path", path)
    newpath = path.replace(rpath, "")
    #print("newpath", newpath)

    #Linux
    if (TargetFlag == "Linux"):
        newpos = projectName.rfind("-")
        filename = projectName[newpos+1:]
        #print("newpos filename" + "/", filename)
        #newpath = "kernel/" + newpath
        newpath = filename + "/" + newpath
    else:
        #Other
        newpos = newpath.find("/")
        newpath = newpath[newpos + 1:]
        #print("newpath2", newpath)

    if ("if" not in branchCode):
        return f"Propagated {branchCode}", None, None
    funcdef = checkOriginFunDef(blameFunc, funcName, funcType, blameLine, branchCode, commitID, newpath)
    if (funcdef!=None):
        sigfDef, diffContent = funcdef
        return sigfDef, diffContent, origTime
    #print("sigFuncVerif funcdef", funcdef)
    return funcdef