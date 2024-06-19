import subprocess
import time 
from random import randint

def randchar():
    alphabet = "abcdefghijklmnopqrstuvwxyz"
    return alphabet[randint(0, 25)]

def compile_cpp_file(file_name):
    command = f"g++ -o tmp {file_name} -DLOCAL -fsanitize=undefined -std=c++20"
    try:
        subprocess.check_output(command, stderr=subprocess.STDOUT, shell=True)
        print("Compilation successful.")
    except subprocess.CalledProcessError as e:
        print(f"Compilation failed with error:\n{e.output.decode()}")

def run_cpp_file_with_input(input_string):
    try:
        input_bytes = input_string.encode()

        # Write the input to a temporary file
        with open("input.txt", "wb") as file:
            file.write(input_bytes)

        # Measure the execution time using the time command-line utility
        start_time = time.time()
        process = subprocess.Popen(["./tmp"], stdin=subprocess.PIPE)
        process.communicate(input_bytes)
        end_time = time.time()

        print(f"\nExecution time: {end_time - start_time} seconds")
    except subprocess.CalledProcessError as e:
        print(f"Program execution failed with error:\n{e.output.decode()}")


compile_cpp_file("tmp.cpp")

input = \
f"""
5
3 7 2 9 2
"""


print(f"Program input:\n{input[:min(100, len(input))]}\n\nProgram Output:\n", sep="")
run_cpp_file_with_input(input)



