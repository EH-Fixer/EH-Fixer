from openai import OpenAI
from tools import save_variable, load_variable
from RewriteAgent import extract_list
from gptTest import CallGPT
import json

example = "For example, the func_a in func_b is missing error handling. The source code of func_b is:\n\
int func_b(int input_b) {int var_a; var_a = func_a()}.\n \
The patch is:\n if (input_b) return NULL; var_a = func_a(); if (var_a) return NULL;\n\
This patch is incorrect since the input_b is not related to the func_a. \
So output: {'Result': 'Fail', 'Irrelevant' : ['if (input_b) return NULL']}.\n\
If the patch is: 'if (var_a) {clean_v(input_b); return NULL;}'. It is correct, so output {'Result': 'Pass', \
'Handling_Actions':['clean_v', 'return NULL'], \
'Code': 'int func_b(int input_b) {int var_a; var_a = func_a(); if (var_a) {clean_v(input_b); return NULL;}'}\n"

outputFormatPrompt = "If there are unnecessary modifications, please output: {'Result': 'Fail', 'Irrelevant' : [lists of unnecessary codes]}.\n\
Otherwise, use this patch to fix the source code, and output {'Result': 'Pass', \
'Handling_Actions': [lists of error-handling functions],'Code': 'Fixed Code'}\n"

def CheckAgent(curPatch, origialCode, errorCode, errFunc, inFunc):
    global example, outputFormatPrompt

    ms = [
        {
            "role": "user",
            "content": f"The {errFunc} in {inFunc} is missing error handling.\
The source code of {inFunc} is as below:\n{origialCode}\n.\
I tried to replace the buggy code with following code snippets: \n{curPatch}\n.\
Please check the patch if it only modify the error handling bugs related to {inFunc}, and output the result in json format.\n"\
+ outputFormatPrompt + example,
        }
    ]
    if (errorCode!=None):
        ms = [
            {
                "role": "user",
                "content": f"The {errFunc} in {inFunc} is missing error handling. \
The source code of {inFunc} is as below:\n{origialCode}\n.\
I tried to replace the buggy code with following code snippets:\n{errorCode}\n\
with the following patch: \n{curPatch}\n.\
Please check the patch if it only modify the error handling bugs related to {inFunc}, and output the result in json format.\n"\
+ outputFormatPrompt + example,
            }
        ]

    ansString = CallGPT(ms)

    return check_json_process(ansString)

def check_json_process(response):
    try:
        json_data = response
        if ('```json' in response):
            start = response.index('```json') + 7
            end = response.rindex('```')
            json_data = response[start:end]
        print("json_process json_data", json_data)
        data = json.loads(json_data)
    except (ValueError, json.JSONDecodeError) as e:
        print("Not found JSON:", e)
        return None

    checkResult = None
    fixedCode = None
    handlingActions = None
    irrInfo = None
    try:
        # 处理JSON数据
        if data['Result'] == 'Pass':
            checkResult = True
            print("Check Passed")
            handlingActions = data["Handling_Actions"]
            fixedCode = data['Code']
        elif data['Result'] == 'Fail':
            checkResult = False
            irrInfo = data['Irrelevant']


    except KeyError as e:
        print("Error JSON Format:", e)
        return None

    return checkResult, handlingActions, fixedCode, irrInfo