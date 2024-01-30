from colorama import Fore, Back, Style


def dev(message: str):
    print(f"{Fore.CYAN}[DEV]{Fore.RESET}  {message}")

def sol(message: str):
    print(f"{Fore.GREEN}[SOL]{Fore.RESET}  {message}")