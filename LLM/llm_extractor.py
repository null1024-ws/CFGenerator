import os
import argparse
import openai
import time
import yaml


class GuardingConditionExtractor:
    def __init__(
        self,
        function_pair_file,
        function_info_file,
        project_path,
        code_dir,
        result_dir,
        prompt_template,
        model_name,
        example,
        query_count,
        query_interval,
    ):
        self.function_pair_file = function_pair_file
        self.function_info_file = function_info_file
        self.project_path = project_path
        self.code_dir = code_dir
        self.result_dir = result_dir
        self.function_info = {}
        self.prompt_template = prompt_template
        self.model_name = model_name
        self.example = example
        self.query_count = query_count
        self.query_interval = query_interval

        self._ensure_directory_exists(self.code_dir)
        self._ensure_directory_exists(self.result_dir)

    @staticmethod
    def _ensure_directory_exists(directory):
        if not os.path.exists(directory):
            os.makedirs(directory)

    def load_function_info(self):
        with open(self.function_info_file, "r") as f:
            for line in f:
                file_name, func_name, start_line, end_line = line.strip().split()
                self.function_info[func_name.strip()] = {
                    "file": file_name,
                    "start_line": int(start_line),
                    "end_line": int(end_line),
                }

    def extract_function_snippet_with_comments(self, func_name):
        func_name = func_name.strip("()").strip()
        if func_name not in self.function_info:
            return None, None

        info = self.function_info[func_name]
        file_path = os.path.join(self.project_path, info["file"])
        if not os.path.exists(file_path):
            return None, None

        with open(file_path, "r") as f:
            lines = f.readlines()

        snippet = lines[info["start_line"] - 1 : info["end_line"]]
        return snippet, info

    def extract_function_snippet(self, func_name, truncate_function):
        func_name = func_name.strip("()").strip()
        if func_name not in self.function_info:
            return None, None

        info = self.function_info[func_name]
        file_path = os.path.join(self.project_path, info["file"])
        if not os.path.exists(file_path):
            return None, None

        with open(file_path, "r") as f:
            lines = f.readlines()

        no_comment_lines = []
        in_block_comment = False

        for line in lines:
            if in_block_comment:
                end_idx = line.find("*/")
                if end_idx != -1:
                    line = line[end_idx + 2 :]
                    in_block_comment = False
                else:
                    no_comment_lines.append("")
                    continue

            line_comment_idx = line.find("//")
            if line_comment_idx != -1:
                line = line[:line_comment_idx]

            start_idx = line.find("/*")
            while start_idx != -1:
                end_idx = line.find("*/", start_idx + 2)
                if end_idx != -1:
                    line = line[:start_idx] + line[end_idx + 2 :]
                    start_idx = line.find("/*", start_idx)
                else:
                    line = line[:start_idx]
                    in_block_comment = True
                    break

            no_comment_lines.append(line)

        lines = no_comment_lines

        # Find end_line by locating truncate_function
        for idx, line in enumerate(
            lines[info["start_line"] - 1 :], start=info["start_line"]
        ):
            if truncate_function in line:
                info["end_line"] = idx
                break

        if "end_line" not in info:
            return None, None

        snippet = lines[info["start_line"] - 2 : info["end_line"]]
        return snippet, info

    def process_function_pairs(self):
        with open(self.function_pair_file, "r") as f:
            for line in f:
                parts = line.strip().split(',')
                caller = parts[0].strip("()").strip()
                callee = parts[1].strip("()").strip()

                # Extract snippets with and without comments
                snippet_with_comments, info_with_comments = self.extract_function_snippet_with_comments(caller)
                snippet_no_comments, info_no_comments = self.extract_function_snippet(caller, callee)

                if snippet_with_comments and info_with_comments:
                    # Save snippet with comments to file
                    self.save_snippet(
                        snippet_with_comments, caller, info_with_comments["start_line"], info_with_comments["end_line"]
                    )

                if snippet_no_comments and info_no_comments:
                    # Process snippet without comments using LLM
                    formatted_snippet = "".join(snippet_no_comments).strip()
                    self.fetch_guarding_condition_multiple_queries(
                        caller,
                        callee,
                        formatted_snippet,
                        self.example,
                        info_no_comments["file"],
                    )

    def save_snippet(self, snippet, func_name, start_line, end_line):
        file_name = f"{func_name}_{start_line}_{end_line}.c"
        file_path = os.path.join(self.code_dir, file_name)
        with open(file_path, "w") as f:
            f.writelines(snippet)

    def fetch_guarding_condition_multiple_queries(
        self, 
        caller, 
        callee, 
        snippet, 
        example, 
        file_name
    ):
        prompt = self.prompt_template.format(
            analyzed_function=snippet,
            caller_function_name=caller,
            callee_function_name=callee,
            example=example,
            file_name=file_name,  # The new placeholder in the template
        )

        openai.api_key = " "

        all_responses = []

        for query_idx in range(self.query_count):
            try:
                response = openai.ChatCompletion.create(
                    model=self.model_name,
                    temperature=0.2,
                    messages=[{"role": "user", "content": prompt}],
                )
                response_content = response.choices[0].message["content"]
                all_responses.append(response_content)
                time.sleep(self.query_interval)  # Delay between queries
            except Exception as e:
                print(f"Query {query_idx + 1} failed for {caller} -> {callee}: {e}")

        # Save all responses to a single file
        self.save_all_guarding_conditions(caller, callee, all_responses)

    def save_all_guarding_conditions(self, caller, callee, responses):
        file_name = f"{caller}_to_{callee}_guarding_condition_all.txt"
        file_path = os.path.join(self.result_dir, file_name)

        with open(file_path, "w") as f:
            for idx, response in enumerate(responses, start=1):
                f.write(f"Response {idx}:\n")
                f.write(response + "\n\n")



if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Extract guarding conditions using LLMs."
    )
    parser.add_argument("function_pair_file", help="Path to function pair file.")
    parser.add_argument("function_info_file", help="Path to function info file.")
    parser.add_argument("project_path", help="Path to C project source files.")
    parser.add_argument("code_dir", help="Directory to store extracted code snippets.")
    parser.add_argument(
        "result_dir", help="Directory to store guarding condition results."
    )
    parser.add_argument("--model_name", default="gpt-4o", help="LLM model name to use.")
    parser.add_argument(
        "--query_count",
        type=int,
        default=4,
        help="Number of times to query the API for each function pair.",
    )
    parser.add_argument(
        "--query_interval",
        type=int,
        default=3,
        help="Interval in seconds between API queries.",
    )

    args = parser.parse_args()

    with open("prompt_template.yml", "r") as template_file:
        yaml_content = yaml.safe_load(template_file)
        prompt_template = yaml_content["template"]

    example = """
Analyzed Function:
```python
int 
xmlNodeDump(xmlBufferPtr buf, xmlDocPtr doc, xmlNodePtr cur, int level, int format)
{
    xmlBufPtr buffer;
    int ret;
    int a = 2;

    if ((buf == NULL) || (cur == NULL))
        return(-1);
    buffer = xmlBufFromBuffer(buf);
    if (buffer == NULL)
        a++;
    ret = xmlBufNodeDump(buffer, doc, cur, level, format);
    xmlBufBackToBuffer(buffer);
    if (ret > INT_MAX)
        return(-1);
    return((int) ret);
}
```
Caller: xmlNodeDump
Callee: xmlBufNodeDump

Output:
[
    {
        "condition": "(buf == NULL) || (cur == NULL)",
        "flag": false,
        "file": xmlsave.c
    }
]
    """

    extractor = GuardingConditionExtractor(
        args.function_pair_file,
        args.function_info_file,
        args.project_path,
        args.code_dir,
        args.result_dir,
        prompt_template,
        args.model_name,
        example,
        args.query_count,
        args.query_interval,
    )

    start_time = time.time()

    extractor.load_function_info()
    extractor.process_function_pairs()

    end_time = time.time()
    print(f"Time taken to analyze: {end_time - start_time:.2f} seconds")

