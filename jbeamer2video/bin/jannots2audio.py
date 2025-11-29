#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
converts extracted annotations from text to audio using Mac's say command.
"""

import sys
import os
import requests

def synthesize_voice(text, filename, speaker=2):
    """
    音声合成を行う。https://zenn.dev/zenn24yykiitos/articles/fff3c954ddf42c を参考にしました。
    Args:
      - text(str): 読み上げテキスト
      - filename(str): 保存先ファイル名 (*.wav)
      - speaker(int): 読み手。デフォルト値の2は「四国めたん, ノーマル」
    Returns: None
    Exception: Exception(エラー発生時)

    speaker 一覧が取得したい場合は https://zenn.dev/zenn24yykiitos/articles/f3e983fe650e08 を
    参考にしてください。
    """
    query_payload = {'text': text, 'speaker': speaker}
    query_response = requests.post(f'http://localhost:50021/audio_query', params=query_payload)
    if query_response.status_code != 200:
        raise Exception(f"Error in audio_query: {query_response.text}")
    query = query_response.json()

    synthesis_payload = {'speaker': speaker}
    synthesis_response = requests.post(f'http://localhost:50021/synthesis', params=synthesis_payload, json=query)
    if synthesis_response.status_code == 200:
        with open(filename, 'wb') as f:
            f.write(synthesis_response.content)
            print(f"{filename} generated.")
    else:
        raise Exception(f"Error in synthesis: {synthesis_response.text}")


def main():
   narrator = sys.argv[1]
   voice = sys.argv[2]
   filepath = sys.argv[3]

   if not os.path.isfile(filepath):
       print("File path {} does not exist. Exiting...".format(filepath))
       sys.exit()
  
   with open(filepath) as fp:
       cnt = 0
       old_frame = 1
       for line in fp:
           # print("line {} contents {}".format(cnt, line))
           if ( len(line) > 1 ):
               if ( line[1] == "*" ):
                   num = int(line[8:11].strip().split(':')[0])
                   print("talk frame at ", num )
                   outfile = "frames/frame{0:03d}.wav".format(num)
                   synthesize_voice(line[11:], outfile, speaker=int(voice))
                   #os.system("say"+' -v '+voice+' "'+line[11:]+'" -o frames/frame{0:03d}.aiff'.format(num))
                   for quiet_frame in range(old_frame,num):
                       print("quiet frame at ",quiet_frame)
                       if (quiet_frame == 1):
                           outfile = "frames/frame{0:03d}.wav".format(quiet_frame)
                           synthesize_voice(
                                f"。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。",
                                outfile,
                                speaker=int(voice)
                           )
                       else:
                           outfile = "frames/frame{0:03d}.wav".format(quiet_frame)
                           synthesize_voice(
                                f"。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。。",
                                outfile,
                                speaker=int(voice)
                           )
                   old_frame=num+1
           cnt += 1
  
if __name__ == '__main__':
    print("jannots2audio starts.")
    main()
