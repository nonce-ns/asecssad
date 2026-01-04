import requests
import json
import os
import time
import glob
import subprocess
import shutil

# --- Konfigurasi File ---
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
PROJECT_ROOT = os.path.join(BASE_DIR, '..')
EXCLUDED_FILES = set() # Semua file akan di-obfuscate dengan tool ini

# --- Konfigurasi API LuaObfuscator ---
API_URL = 'https://luaobfuscator.com/api/ide/obfuscateAll/pre-6/6'

# API Key Authentication
API_KEY = "31d0ac42-da92-2d08-a2e8-39ddc06fa5c461d0"

headers = {
    'apikey': API_KEY,  # Menggunakan API Key
    'content-type': 'application/json'
}

# Cookies tidak lagi diperlukan dengan API Key
cookies = {}

def get_lua_files():
    # Cari semua file .lua di folder parent
    lua_files = glob.glob(os.path.join(PROJECT_ROOT, "*.lua"))
    # Filter file yang sudah diobfuscate agar tidak diobfuscate ulang
    files = [
        f for f in lua_files
        if "_obfuscated.lua" not in f
    ]
    return sorted(files)

def push_to_github(commit_msg_filename, paths_to_add=None):
    """
    Melakukan git add, commit, dan push.
    commit_msg_filename: Nama file untuk pesan commit, atau string custom.
    paths_to_add: List path yang ingin di-add. Jika None, tambah folder obfuscator.
    """
    print(f"\n[git] Memulai proses upload ke GitHub...")
    
    try:
        # Pindah ke root repo (sekarang di folder obfuscator)
        os.chdir(BASE_DIR)
        
        # 1. Git Add
        if paths_to_add is None:
            # Jika None, add semua (.)
            print(f"[git] Adding all files...")
            subprocess.run(["git", "add", "."], check=True)
        else:
            # Jika ada list file, add spesifik (gunakan basename karena kita sudah di BASE_DIR)
            rel_paths = [os.path.basename(p) for p in paths_to_add]
            print(f"[git] Adding selected files: {rel_paths}")
            subprocess.run(["git", "add", "--"] + rel_paths, check=True)
        
        # 2. Git Commit
        commit_message = f"Update file: {commit_msg_filename}"
        print(f"[git] Committing with message: '{commit_message}'...")
        # Gunakan check=False karena jika tidak ada perubahan, git commit return code 1
        subprocess.run(["git", "commit", "-m", commit_message], check=False)
        
        # 3. Git Push
        print(f"[git] Pushing to origin main...")
        
        # Pull dulu untuk menghindari konflik (izinkan unrelated history)
        print(f"[git] Pulling latest changes...")
        subprocess.run(["git", "pull", "origin", "main", "--allow-unrelated-histories", "--no-edit"], check=False)
        
        # Push langsung ke main
        result = subprocess.run(["git", "push", "origin", "main"], stderr=subprocess.PIPE, text=True) 
        
        if result.returncode != 0:
             print(f"[-] Push gagal. Cek detail:\n{result.stderr}")
        else:
             print(f"[+] Push berhasil ke main!")

        print(f"[+] SELESAI! Upload ke GitHub berhasil.")
        
    except subprocess.CalledProcessError as e:
        print(f"[-] Git Error: {e}")
    except Exception as e:
        print(f"[-] Error: {e}")

def obfuscate_file(input_path, auto_push=True):
    filename = os.path.basename(input_path)
    output_path = os.path.join(BASE_DIR, filename)

    print(f"\n[+] Memproses: {filename}...")
    
    try:
        with open(input_path, 'r', encoding='utf-8') as f:
            script_content = f.read()
    except Exception as e:
        print(f"[-] Gagal membaca file: {e}")
        return

    # STEP 1: Upload Script (newscript)
    print("[1/2] Mengupload script...")
    try:
        # Endpoint baru untuk create session
        new_script_url = "https://luaobfuscator.com/api/obfuscator/newscript"
        
        # Kirim script sebagai RAW BODY (sesuai docs umum mereka)
        response_new = requests.post(new_script_url, headers=headers, data=script_content)
        
        if response_new.status_code != 200:
             print(f"[-] Upload Gagal (HTTP {response_new.status_code}): {response_new.text}")
             return

        try:
            data_new = response_new.json()
            session_id = data_new.get("sessionId")
        except:
            print("[-] Gagal parsing JSON dari newscript.")
            return

        if not session_id:
            print("[-] Session ID tidak ditemukan.")
            return
            
        print(f"[+] Sesi dibuat: {session_id}")

        # STEP 2: Obfuscate (obfuscate)
        print("[2/2] Mengirim perintah obfuscate...")
        obfuscate_url = "https://luaobfuscator.com/api/obfuscator/obfuscate"
        
        # Header perlu ditambah Session-Id
        auth_headers = headers.copy()
        auth_headers["sessionId"] = session_id
        
        # Config Body
        config = {
            "MinifyAll": False, # Jangan minify agar masih bisa debug kalau error
            "Virtualize": True, # Virtualization (IronBrew)
            "CustomByteCode": True,
            "ControlFlowFlattening": True,
            "EncryptStrings": True,
            # Preset bisa diatur manual lewat flag-flag ini
        }
        
        response_obf = requests.post(obfuscate_url, headers=auth_headers, json=config)
        
        if response_obf.status_code == 200:
            try:
                data_obf = response_obf.json()
                final_code = data_obf.get("code")
            except:
                final_code = response_obf.text

            if final_code:
                with open(output_path, 'w', encoding='utf-8') as f:
                    f.write(final_code)
                print(f"[+] SUKSES! Disimpan di: {os.path.basename(output_path)}")
                
                if auto_push:
                    push_to_github(filename, paths_to_add=[output_path])
            else:
                print("[-] Hasil obfuscate kosong.")
        else:
             print(f"[-] Obfuscate Gagal (HTTP {response_obf.status_code}): {response_obf.text}")

    except Exception as e:
        print(f"[-] Exception: {e}")

def main():
    while True:
        print("="*60)
        print("   LUAOBFUSCATOR.COM API & GITHUB PUSHER")
        print("   (Good for sell.lua & advanced scripts)")
        print("="*60)

        files = get_lua_files()
        
        if not files:
            print("[-] Tidak ada file .lua yang ditemukan di folder project.")
            return

        # Opsi All Scripts
        print("0.  [ALL SCRIPTS] Obfuscate & Upload SEMUA") 
        print("-" * 30)

        print("Pilih file untuk diobfuscate & upload:")
        for idx, f in enumerate(files, 1):
            name = os.path.basename(f)
            print(f"{idx}. {name}")
        print(f"{len(files) + 1}. Keluar")

        try:
            choice = input("\nMasukkan nomor pilihan: ")
            if not choice.isdigit():
                print("[-] Harap masukkan angka.\n")
                continue
            
            idx = int(choice)
            
            if idx == 0:
                print("\n" + "="*40)
                print("   MEMPROSES SEMUA FILE...")
                print("="*40)
                
                # 1. Obfuscate semua tanpa push dulu
                for f in files:
                    obfuscate_file(f, auto_push=False)

                # 2. Push satu kali di akhir
                print("\n" + "="*40)
                print("   MENGUPLOAD SEMUA HASIL KE GITHUB...")
                print("="*40)
                push_to_github("BATCH UPDATE (Using LuaObfuscator)", paths_to_add=None)
                
            elif 1 <= idx <= len(files):
                target_file = files[idx - 1]
                obfuscate_file(target_file, auto_push=True)
                
            elif idx == len(files) + 1:
                print("Sampai jumpa!")
                break  # Keluar dari loop
            else:
                print("[-] Pilihan tidak valid.\n")
                continue
                
            print()  # Baris kosong sebelum menu muncul lagi
                
        except KeyboardInterrupt:
            print("\nOperasi dibatalkan.")
            break

if __name__ == "__main__":
    main()
