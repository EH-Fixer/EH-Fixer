from openai import OpenAI
from tools import save_variable, load_variable
from RewriteAgent import extract_list, json_process
from CheckAgent import CheckAgent
from ConfigFile import apiKey, baseUrl
import http.client
import json
from gptTest import CallGPT
import re

repDict = {}


"Please return the diagnostic results in the following JSON format:\n\
1. If no error handling is needed, return {'Flag': 'False', 'Functions': [list of function names need further fix]}.\n\
2. If the error can be directly fixed, return {'Flag': True, 'Code': '[Corrected Code Segment]'}.\n\
3. If more information is needed to determine an error handling strategy, \
return {'Flag': 'MoreInfo', 'InfoType': '[Choose: Function Name | Data Type | Other Information]'}."

saveTempPrompt = "Please help me fix the error handling bug.\n\
Input: the line of code containing error-handling bug and the function it is in, the related call relationship and source code, the handling code for the error in other locations, and other error handling code nearby the error.\n\
Output:\n\
1.If no error handling is needed, return {'Flag': 'Pass', 'Functions': [list of function names need further fix]}. \n\
2.If the error can be directly fixed, return {'Flag': 'Fix', 'Code': 'correct code snippets', 'Need_Fix': [list of function names need further fix]}\
3.If more information is needed to determine the error-handling strategy, return {'Flag': 'IR', \
'More_Info': {'Need_Code': [list of function names need provide source code],\
'Need_Clean_Method': [list of data types need provide clean up method]\
'Other': 'Other Information'}}\
An example is given below:\n\
{'role': 'user', 'Prompt': '\
func_a is missing error handling in func_b.\n\
The line containing error-handling bug is err1 = func_a()\
func_b is called by func_c, func_d, func_e.\n\
The related code is as follows:\n\
int func_b() {int err1;\n err1 = func_a();\n usage1(err1);}\n\
int func_c() {int err2 = func_b();\n usage2(err2);}\n\
int func_d() {return func_b();}.\n\
Error handling for func_a in other functions:\n\
int err = func_a();\n\
if (err) return ErrCode1.\n\
Error handling in the same file as func_b:\n\
if (err) {logErr(); return ErrCode2;}.'\n\
In the above example, first, based on the error handling of func_a in other functions, it can be inferred that an error occurs when the return value of func_a is NULL;\n\
and then, based on the source code of func_b, and the error handling of func_a in other functions, it is inferred that the error is relatively severe;\n\
and lastly, the combination of the severity of func_a, the error handling of func_a in other functions, and other error handling code snippets in the same file with func_b, the appropriate error handling actions are selected for func_a.\n\
As for the FurtherFix, since the error handling chosen for a requires the return of an error code, it is necessary to see if, after repair, the error in func_b might propagate to other functions. func_c has no check on the return value of func_b, so further repair may be needed. func_d has no check, but since it simply passes on the error, it does not need further repair.\
Therefore your output should be:\n\
{'Flag': True, 'Code': 'err1 = func_a();\n\
if (err1){\n\
    logErr();\n\
    return ErrCode1;\n'\
, 'Need_Fix': ['func_c']}."

def oneshotPrompt():#One Shot
    #global patchMessage
    examplePrompt = "Please help me fix the error handling bug and output in json format.\n\
1.If no error handling is needed, output {'Flag': 'Pass', 'Functions': [list of function names need further fix]}. \n\
2.If the error can be directly fixed, output {'Flag': 'Fix', 'Code': 'correct code snippets', 'Need_Fix': [list of function names need further fix]}.\
If the fixed needs to return an error code, 'Need_Fix' stores functions that called the buggy function and could not handle the propagated error.\n\
For example, given two functions: void func_b() {func_a();} void func_c() { int ans_a = func_a(); usage(ans_a);}. \
If we fix a error-handling bug in func_a, and return NULL. func_b didn't use the return value of the func_a, so it will not cause any problem. \
func_c didn't handle the NULL returned from func_a. Therefore, in this case, the 'Need_Fix' should be ['func_c']\
3.If more information is needed to determine the error-handling strategy, output {'Flag': 'IR', \
'More_Info': {'Need_Code': [list of function names need provide source code],\
'Need_Clean_Method': [list of data types need provide clean up method]\
'Other': 'Other Information'}}\
An example output is given below:\n\
{'Flag': True, 'Code': 'err1 = func_a();\n\
if (err1){\n\
logErr();\n\
return ErrCode1;\n'\
, 'Need_Fix': ['func_c']}."

    gptAns = "Based on your request, could you please provide the error message and the relevant function where the error occurs? Additionally, if there's any existing error handling code in other functions or nearby the error, please provide that as well. This information will help me generate the appropriate fix and identify any further functions that may need error handling adjustments."

    oneshotPrompt = [
        {
            "role": "user",
            "content": examplePrompt,
        },
        {
            "role": "GPT",
            "content": gptAns,
        }
    ]
    return oneshotPrompt

def PatchGenerate(orignPrompt, historicalPrompt):
    #orignPrompt = orignPrompt.replace('\\n', '\n')
    ms = [
        {
            "role": "user",
            "content": orignPrompt,
        }
    ]
    if (orignPrompt != None):
        historicalPrompt.extend(ms)
    print("PatchGenerate historicalPrompt")
    for converID, sigconver in enumerate(historicalPrompt):
        print("converID-------------------------------------------------------", converID)
        print("role:", sigconver['role'])
        print("content\n", sigconver['content'])

    nextStage = input("PatchGenerate Debug")
    generated_text = CallGPT(historicalPrompt)
    print("PatchGenerate", generated_text)
    tempt = json_process(generated_text)
    if (tempt == None):
        return None
    Flag, patch, nextFunctions, Need_Code_Lists, Need_Clean_Method_Lists = tempt
    if (Flag == 'Pass' or Flag == 'Fix'):
        return 1, generated_text, patch, nextFunctions
    elif (Flag == 'IR'):
        return 2, generated_text, [Need_Code_Lists, Need_Clean_Method_Lists], nextFunctions
    else:
        return None

def ListRep(str_list):
    global repDict
    slen = len(str_list)
    for i in range(slen):
        if str_list[i] in repDict:
            str_list[i] = repDict[str_list[i]]

severity_descriptions = [
        "logging the error only",
        "logging the error and terminating the program",
        "executing cleanup functions only",
        "executing cleanup functions and terminating the program",
        "completely killing the entire system"
    ]

def generate_prompt_for_error_handling(collectedCodeList):

    prompt = ""

    for i, code_snippets in enumerate(collectedCodeList):
        if code_snippets:
            prompt += f"Strategy {i + 1} ({severity_descriptions[i]}):\n"
            for snippet in code_snippets:
                # 添加代码段
                prompt += f"- {snippet}\n"

    return prompt.strip()



